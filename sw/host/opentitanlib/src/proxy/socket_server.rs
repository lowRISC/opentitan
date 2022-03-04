// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use mio::event::Event;
use mio::net::TcpListener;
use mio::net::TcpStream;
use mio::{Events, Interest, Poll, Token};
use mio_signals::{Signal, SignalSet, Signals};
use serde::de::DeserializeOwned;
use serde::Serialize;
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::HashMap;
use std::io::{ErrorKind, Read, Write};
use std::marker::PhantomData;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::CommandHandler;

const BUFFER_SIZE: usize = 8192;
const EOL_CODE: u8 = b'\n';

fn get_next_token() -> Token {
    static TOCKEN_COUNTER: AtomicUsize = AtomicUsize::new(0);
    Token(TOCKEN_COUNTER.fetch_add(1, Ordering::Relaxed))
}

/// This struct listens on a TCP socket, and maintains a number of concurrent connections,
/// receiving serialized JSON representations of `Msg`, passing them to the given
/// `CommandHandler` to obtain responses to be sent as socket flow contol permits.  Note that
/// this implementaion is not specific to (and does not refer to) any particular protocol.
pub struct JsonSocketServer<Msg: DeserializeOwned + Serialize, T: CommandHandler<Msg>> {
    command_handler: T,
    poll: Poll,
    socket: TcpListener,
    socket_token: Token,
    signals: Signals,
    signal_token: Token,
    connection_map: HashMap<Token, Connection>,
    exit_requested: bool,
    phantom: PhantomData<Msg>,
}

impl<Msg: DeserializeOwned + Serialize, T: CommandHandler<Msg>> JsonSocketServer<Msg, T> {
    pub fn new(command_handler: T, mut socket: TcpListener) -> Result<Self> {
        let poll = Poll::new()?;
        let socket_token = get_next_token();
        poll.registry()
            .register(&mut socket, socket_token, Interest::READABLE)?;
        // Create a `Signals` instance that will catch given set of signals for us.
        let signals: SignalSet = Signal::Terminate | Signal::Interrupt;
        let mut signals = Signals::new(signals)?;
        // And register it with our `Poll` instance.
        let signal_token = get_next_token();
        poll.registry()
            .register(&mut signals, signal_token, Interest::READABLE)?;
        Ok(Self {
            command_handler,
            poll,
            socket,
            socket_token,
            signals,
            signal_token,
            connection_map: HashMap::new(),
            exit_requested: false,
            phantom: PhantomData,
        })
    }

    pub fn run_loop(&mut self) -> Result<()> {
        let mut events = Events::with_capacity(1024);
        while !self.exit_requested {
            self.poll.poll(&mut events, None)?;
            for event in events.iter() {
                if event.token() == self.socket_token {
                    self.process_new_connection()?;
                } else if event.token() == self.signal_token {
                    self.process_signals()?;
                } else {
                    match self.process_connection(event) {
                        Ok(shutdown) => {
                            if shutdown {
                                self.shutdown_connection(event)?;
                            }
                        }
                        Err(e) => {
                            log::warn!("Connection {:#X} error: {}", event.token().0, e,);
                            self.shutdown_connection(event)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Accept new socket connections, creating new Connection objects.
    fn process_new_connection(&mut self) -> Result<()> {
        loop {
            match self.socket.accept() {
                Ok((mut conn_socket, _addres)) => {
                    let token = get_next_token();
                    log::info!("New connection id:{:#X}", token.0);
                    match self.connection_map.entry(token) {
                        Vacant(entry) => {
                            self.poll.registry().register(
                                &mut conn_socket,
                                token,
                                Interest::READABLE | Interest::WRITABLE,
                            )?;
                            entry.insert(Connection::new(conn_socket));
                        }
                        Occupied(_) => {
                            panic!("JsonSocketServer error: token colision");
                        }
                    };
                }
                Err(err) if err.kind() == ErrorKind::WouldBlock => {
                    // No more connections ready to accept (or spurious poll event).
                    return Ok(());
                }
                Err(err) => bail!("Error accepting TCP connection: {}", err),
            }
        }
    }

    fn process_signals(&mut self) -> Result<()> {
        loop {
            match self.signals.receive()? {
                Some(Signal::Interrupt) => {
                    log::info!("Got interrupt signal");
                    self.exit_requested = true;
                }
                Some(Signal::Terminate) => {
                    log::info!("Got terminate signal");
                    self.exit_requested = true;
                }
                Some(signal) => {
                    log::info!("Got unexpected signal: {:?}", signal);
                }
                None => return Ok(()),
            }
        }
    }

    /// Read and write as much as possible from one particular socket connection.
    fn process_connection(&mut self, event: &Event) -> Result<bool> {
        match self.connection_map.get_mut(&event.token()) {
            Some(conn) => {
                if event.is_writable() {
                    conn.write()?;
                }
                if event.is_readable() {
                    conn.read()?;
                    Self::process_any_requests(conn, &self.command_handler)?;
                }
                // Return whether this connection object should be dropped.
                return Ok((conn.rx_eof && (conn.tx_buf.len() == 0)) || conn.broken);
            }
            None => bail!("Connection don't exist token:{:#X}", event.token().0),
        }
    }

    /// Close a socket connection and remove it from the poll list.
    fn shutdown_connection(&mut self, event: &Event) -> Result<()> {
        log::info!("Closing connection id:{:#X}", event.token().0);
        let mut conn = self
            .connection_map
            .remove(&event.token())
            .expect("Missing connection this should never happend!!!");
        self.poll.registry().deregister(&mut conn.socket)?;
        // As `conn` runs out of scope here, its `drop()` method will close the OS handle, which
        // in turn causes TCP/IP connection shutdown to be signalled to the remote end.
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

    // Look for any completely received requests in the rx_buf, and handle them one by one.
    fn process_any_requests(conn: &mut Connection, command_handler: &T) -> Result<()> {
        while let Some(request) = Self::get_complete_request(conn)? {
            // One complete request received, execute it.
            let resp = command_handler.execute_cmd(&request)?;
            // Encode response into tx_buf.
            serde_json::to_writer(&mut conn.tx_buf, &resp)?;
            conn.tx_buf.push(EOL_CODE);
            // Transmit as much as possible without blocking, leaving any remnant in
            // tx_buf.  poll() will tell us when more can be written.
            conn.write()?;
        }
        Ok(())
    }
}

/// Represents one connection with a remote OpenTitan tool invocation.
struct Connection {
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

    // Fill rx_buf with as much data as is available on the socket.
    fn read(&mut self) -> Result<()> {
        let mut rx_buf_len: usize = self.rx_buf.len();
        loop {
            self.rx_buf.resize(rx_buf_len + BUFFER_SIZE, 0);
            match self.socket.read(&mut self.rx_buf[rx_buf_len..]) {
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
        while self.tx_buf.len() > 0 {
            match self.socket.write(&self.tx_buf) {
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
