// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::ErrorKind;
use std::marker::PhantomData;
use std::sync::Arc;

use anyhow::{Context, Result};
use serde::Serialize;
use serde::de::DeserializeOwned;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::Mutex;

use super::CommandHandler;

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
                conn_socket.set_nodelay(true)?;

                let (conn_rx, conn_tx) = conn_socket.into_split();
                // `conn_tx` is used both for unsolicited messages and response messages.
                let conn_tx = Arc::new(Mutex::new(conn_tx));

                let conn_arc = Arc::new(Connection::new(conn_tx.clone()));

                let id = id_counter;
                id_counter += 1;
                log::info!("New connection id:{:#X}", id);

                let sender_clone = sender.clone();
                set.spawn(async move {
                    if let Err(err) =
                        Self::process_connection(sender_clone, conn_arc, conn_rx, conn_tx).await
                    {
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

        tokio::select! {
            r = listener => r,
            r = handler => r,
        }
    }

    async fn transmit_outgoing_msg<M: Serialize>(
        conn_tx: &Mutex<OwnedWriteHalf>,
        msg: M,
    ) -> Result<()> {
        // Encode response into tx_buf.
        let mut tx_buf = serde_json::to_vec(&msg)?;
        tx_buf.push(b'\n');

        let mut tx = conn_tx.lock().await;
        tx.write_all(&tx_buf).await?;
        Ok(())
    }

    /// Read and write as much as possible from one particular socket connection.
    async fn process_connection(
        sender: tokio::sync::mpsc::Sender<(
            Arc<Connection>,
            Msg,
            tokio::sync::oneshot::Sender<Msg>,
        )>,
        conn_arc: Arc<Connection>,
        conn_rx: OwnedReadHalf,
        conn_tx: Arc<Mutex<OwnedWriteHalf>>,
    ) -> Result<()> {
        let mut conn_rx = tokio::io::BufReader::new(conn_rx);
        let mut buf = Vec::new();

        loop {
            buf.clear();
            let len = conn_rx.read_until(b'\n', &mut buf).await?;
            if len == 0 {
                if !buf.is_empty() {
                    anyhow::bail!(std::io::Error::new(
                        ErrorKind::UnexpectedEof,
                        "Server unexpectedly closed connection"
                    ));
                }
                break;
            }

            let request = serde_json::from_slice::<Msg>(&buf)?;

            let (resp_send, resp_recv) = tokio::sync::oneshot::channel();
            sender
                .send((conn_arc.clone(), request, resp_send))
                .await
                .unwrap();
            let resp = resp_recv.await?;
            Self::transmit_outgoing_msg(&conn_tx, resp).await?;
        }

        Ok(())
    }
}

/// Represents one connection with a remote OpenTitan tool invocation.
pub struct Connection {
    #[allow(unused)]
    conn_tx: Arc<Mutex<OwnedWriteHalf>>,
}

impl Connection {
    fn new(conn_tx: Arc<Mutex<OwnedWriteHalf>>) -> Self {
        Self { conn_tx }
    }
}
