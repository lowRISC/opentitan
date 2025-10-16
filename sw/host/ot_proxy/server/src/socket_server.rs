// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::ErrorKind;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};
use std::task::Poll;

use anyhow::{Context, Result};
use serde::Serialize;
use serde::de::DeserializeOwned;
use tokio::net::TcpListener;
use tokio::net::TcpStream;

use super::CommandHandler;

const BUFFER_SIZE: usize = 8192;
const EOL_CODE: u8 = b'\n';

/// This struct listens on a TCP socket, and maintains a number of concurrent connections,
/// receiving serialized JSON representations of `Msg`, passing them to the given
/// `CommandHandler` to obtain responses to be sent as socket flow contol permits.  Note that
/// this implementaion is not specific to (and does not refer to) any particular protocol.
pub struct JsonSocketServer<Msg: DeserializeOwned + Serialize, T: CommandHandler<Msg>> {
    command_handler: T,
    socket: TcpListener,
    phantom: PhantomData<Msg>,
}

impl<Msg: DeserializeOwned + Serialize + Send + 'static, T: CommandHandler<Msg> + 'static>
    JsonSocketServer<Msg, T>
{
    pub fn new(command_handler: T, socket: TcpListener) -> Result<Self> {
        Ok(Self {
            command_handler,
            socket,
            phantom: PhantomData,
        })
    }

    pub async fn run_loop(&mut self) -> Result<()> {
        // Create a local set to allow `spawn_local`. This is needed as majority of opentitanlib is not
        // multi-thread-safe currently.
        let local_set = tokio::task::LocalSet::new();
        let _local_set_guard = local_set.enter();

        // Store all connections in a join set so they're aborted when terminating.
        let mut set = tokio::task::JoinSet::new();
        let mut id_counter = 0;

        // Since opentitanlib is mostly not multi-thread-safe, we have to stay on this thread to deal with
        // `command_handler`.
        // We do this by using a mpsc queue that each connection can push to.
        let (sender, mut recv) = tokio::sync::mpsc::channel(32);

        let listener = async {
            loop {
                // Drain connections that are already completed.
                while set.try_join_next().is_some() {}

                let (conn_socket, _address) = self
                    .socket
                    .accept()
                    .await
                    .context("Error accepting TCP connection")?;

                let conn_arc = Arc::new(Mutex::new(Connection::new(conn_socket)));

                let id = id_counter;
                id_counter += 1;
                log::info!("New connection id:{:#X}", id);

                let sender_clone = sender.clone();
                set.spawn(async move {
                    if let Err(err) = Self::process_connection(sender_clone, conn_arc).await {
                        log::warn!("Connection {:#X} error: {}", id, err);
                    }

                    log::info!("Closing connection id:{:#X}", id);
                });
            }

            // Type hint
            #[allow(unreachable_code)]
            Ok::<(), anyhow::Error>(())
        };

        let handler = async {
            loop {
                let (conn_arc, request, resp_send) =
                    recv.recv().await.expect("recv shouldn't be dropped");
                let resp = self.command_handler.execute_cmd(&conn_arc, &request)?;
                // Ignore error which indicates the connection has been closed.
                let _ = resp_send.send(resp);
            }

            // Type hint
            #[allow(unreachable_code)]
            Ok::<(), anyhow::Error>(())
        };

        // Ensure that the local set never completes so we can keep polling it using `select!`.
        local_set.spawn_local(std::future::pending::<()>());

        tokio::select! {
            r = listener => r,
            r = handler => r,
            _ = local_set => unreachable!(),
        }
    }

    /// Read and write as much as possible from one particular socket connection.
    async fn process_connection(
        sender: tokio::sync::mpsc::Sender<(
            Arc<Mutex<Connection>>,
            Msg,
            tokio::sync::oneshot::Sender<Msg>,
        )>,
        conn_arc: Arc<Mutex<Connection>>,
    ) -> Result<()> {
        loop {
            let (readable, writable) = std::future::poll_fn(|cx| -> Poll<Result<_>> {
                let conn = conn_arc.lock().unwrap();
                let need_poll_write = !conn.tx_buf.is_empty();

                let read_poll = conn.socket.poll_read_ready(cx)?;
                let write_poll = if need_poll_write {
                    conn.socket.poll_write_ready(cx)?
                } else {
                    Poll::Pending
                };

                match (read_poll, write_poll) {
                    (Poll::Pending, Poll::Pending) => Poll::Pending,
                    (Poll::Ready(()), _) => Poll::Ready(Ok((true, write_poll.is_ready()))),
                    _ => Poll::Ready(Ok((false, true))),
                }
            })
            .await?;

            {
                let mut conn = conn_arc.lock().unwrap();
                if writable {
                    conn.write()?;
                }
                if readable {
                    conn.read()?;
                }

                if (conn.rx_eof && (conn.tx_buf.is_empty())) || conn.broken {
                    break;
                }
            }

            #[allow(clippy::let_and_return)]
            while let Some(request) = {
                let v = Self::get_complete_request(&mut conn_arc.lock().unwrap())?;
                v
            } {
                let (resp_send, resp_recv) = tokio::sync::oneshot::channel();
                sender
                    .send((conn_arc.clone(), request, resp_send))
                    .await
                    .unwrap();
                let resp = resp_recv.await?;
                conn_arc.lock().unwrap().transmit_outgoing_msg(resp)?;
            }
        }

        Ok(())
    }

    /// Check if the buffer contains at least one full JSON request.  If so, remove it from the
    /// buffer, decode and return it.
    fn get_complete_request(conn: &mut Connection) -> Result<Option<Msg>> {
        if let Some(n) = conn.rx_buf.iter().position(|c| *c == EOL_CODE) {
            let res = serde_json::from_slice::<Msg>(&conn.rx_buf[..n])?;
            if n + 1 < conn.rx_buf.len() {
                // Shuffling bytes around in a Vec is expensive, but realistically, as the
                // clients would be waiting for response to each request before sending the next
                // request, this code will rarely if ever execute.
                conn.rx_buf.rotate_left(n + 1);
            }
            conn.rx_buf.resize(conn.rx_buf.len() - n - 1, 0);
            return Ok(Some(res));
        }
        Ok(None)
    }
}

/// Represents one connection with a remote OpenTitan tool invocation.
pub struct Connection {
    socket: TcpStream,
    /// Outgoing data waiting to be written when the socket permits.
    tx_buf: Vec<u8>,
    /// Data received from the remote end, but not yet decoded into `Msg`.
    rx_buf: Vec<u8>,
    /// The remote end indicated end-of-stream.  After processing any remaning data in `rx_buf`,
    /// this Connection should be gracefully shut down and dropped.
    rx_eof: bool,
    /// Some error happened during writing or reading from the socket, we cannot meaningfully
    /// continue processing, and the connection should be dropped as soon as possible.
    broken: bool,
}

impl Connection {
    fn new(soc: TcpStream) -> Self {
        Self {
            socket: soc,
            tx_buf: Vec::new(),
            rx_buf: Vec::new(),
            rx_eof: false,
            broken: false,
        }
    }

    pub fn transmit_outgoing_msg<T: Serialize>(&mut self, msg: T) -> Result<()> {
        // Encode response into tx_buf.
        serde_json::to_writer(&mut self.tx_buf, &msg)?;
        self.tx_buf.push(EOL_CODE);
        // Transmit as much as possible without blocking, leaving any remnant in
        // tx_buf.  poll() will tell us when more can be written.
        self.write()?;
        Ok(())
    }

    // Fill rx_buf with as much data as is available on the socket.
    fn read(&mut self) -> Result<()> {
        let mut rx_buf_len: usize = self.rx_buf.len();
        loop {
            self.rx_buf.resize(rx_buf_len + BUFFER_SIZE, 0);
            match self.socket.try_read(&mut self.rx_buf[rx_buf_len..]) {
                Ok(0) => {
                    self.rx_eof = true;
                    break;
                }
                Ok(n) => {
                    rx_buf_len += n;
                }
                Err(err) => {
                    if err.kind() != ErrorKind::WouldBlock {
                        self.broken = true;
                    }
                    break; // Break out of loop, also on expected WouldBlock
                }
            }
        }
        self.rx_buf.resize(rx_buf_len, 0);
        Ok(())
    }

    // Transmit as much data out of tx_buf as socket will allow.
    fn write(&mut self) -> Result<()> {
        while !self.tx_buf.is_empty() {
            match self.socket.try_write(&self.tx_buf) {
                Ok(n) => {
                    if n < self.tx_buf.len() {
                        // Shuffling bytes around in a Vec is expensive, but realistically, as
                        // the clients would be waiting for response to each request before
                        // sending the next request, it is unlikely that the OS transmit buffer
                        // would ever fill up and cause partial writes.
                        self.tx_buf.rotate_left(n);
                    }
                    self.tx_buf.resize(self.tx_buf.len() - n, 0);
                }
                Err(err) => {
                    if err.kind() != ErrorKind::WouldBlock {
                        self.broken = true;
                    }
                    break;
                }
            }
        }
        Ok(())
    }
}
