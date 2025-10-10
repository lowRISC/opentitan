// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use handler::TransportCommandHandler;
use protocol::Message;
use socket_server::{Connection, JsonSocketServer};
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::net::TcpListener;

use crate::app::TransportWrapper;

pub mod errors;
mod handler;
mod nonblocking_uart;
pub mod protocol;
mod socket_server;

/// Interface for handlers of protocol messages, responding to each message with a single
/// instance of the same protocol message.
pub trait CommandHandler<Msg> {
    fn execute_cmd(&mut self, conn: &Arc<Connection>, msg: &Msg) -> Result<Msg>;
}

/// This is the main entry point for the session proxy.  This struct will either bind on a
/// specified port, or find an available port from a range, before entering an event loop.
pub struct SessionHandler {
    port: u16,
    socket_server: JsonSocketServer<Message, TransportCommandHandler>,
}

impl SessionHandler {
    pub fn init(transport: TransportWrapper, listen_port: Option<u16>) -> Result<Self> {
        let mut port = listen_port.unwrap_or(9900);
        let limit = listen_port.unwrap_or(9999);
        // Find a suitable port to bind to.
        let socket = loop {
            let addr = SocketAddr::from(([0u8; 4], port));
            match crate::util::runtime::block_on(async { TcpListener::bind(addr).await }) {
                Ok(socket) => break socket,
                Err(e) if port >= limit => bail!(e),
                Err(_) => port += 1,
            }
        };
        let socket_server =
            JsonSocketServer::new(TransportCommandHandler::new(transport)?, socket)?;
        Ok(Self {
            port,
            socket_server,
        })
    }

    pub fn get_port(&self) -> u16 {
        self.port
    }

    pub fn run_loop(&mut self) -> Result<()> {
        crate::util::runtime::block_on(crate::util::runtime::with_graceful_shutdown(
            self.socket_server.run_loop(),
        ))
    }
}
