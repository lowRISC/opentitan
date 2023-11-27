// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use handler::TransportCommandHandler;
use mio::event::Event;
use mio::net::TcpListener;
use mio::{Registry, Token};
use nonblocking_uart::NonblockingUartRegistry;
use protocol::Message;
use socket_server::{Connection, JsonSocketServer};
use std::collections::HashMap;
use std::net::SocketAddr;

use crate::app::TransportWrapper;

pub mod errors;
mod handler;
mod nonblocking_uart;
pub mod protocol;
mod socket_server;

/// Interface for handlers of protocol messages, responding to each message with a single
/// instance of the same protocol message.
pub trait CommandHandler<Msg, E: ExtraEventHandler> {
    fn execute_cmd(
        &mut self,
        conn_token: Token,
        registry: &Registry,
        extra_event_handler: &mut E,
        msg: &Msg,
    ) -> Result<Msg>;

    fn register_nonblocking_help(
        &self,
        _registry: &mio::Registry,
        _token: mio::Token,
    ) -> Result<()> {
        Ok(())
    }

    fn nonblocking_help(&self) -> Result<()> {
        Ok(())
    }
}

pub trait ExtraEventHandler {
    fn handle_poll_event(
        &mut self,
        event: &Event,
        connection_map: &mut HashMap<Token, Connection>,
    ) -> Result<bool>;
}

/// This is the main entry point for the session proxy.  This struct will either bind on a
/// specified port, or find an available port from a range, before entering an event loop.
pub struct SessionHandler<'a> {
    port: u16,
    socket_server: JsonSocketServer<Message, TransportCommandHandler<'a>, NonblockingUartRegistry>,
}

impl<'a> SessionHandler<'a> {
    pub fn init(transport: &'a TransportWrapper, listen_port: Option<u16>) -> Result<Self> {
        let mut port = listen_port.unwrap_or(9900);
        let limit = listen_port.unwrap_or(9999);
        // Find a suitable port to bind to.
        let socket = loop {
            let addr = SocketAddr::from(([0u8; 4], port));
            match TcpListener::bind(addr) {
                Ok(socket) => break socket,
                Err(e) if port >= limit => bail!(e),
                Err(_) => port += 1,
            }
        };
        let socket_server = JsonSocketServer::new(
            TransportCommandHandler::new(transport)?,
            NonblockingUartRegistry::new(),
            socket,
        )?;
        Ok(Self {
            port,
            socket_server,
        })
    }

    pub fn get_port(&self) -> u16 {
        self.port
    }

    pub fn run_loop(&mut self) -> Result<()> {
        self.socket_server.run_loop()
    }
}
