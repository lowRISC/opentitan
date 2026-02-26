// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::rc::Rc;
use std::task::{Context, Poll};

use anyhow::Result;

use crate::io::console::{ConsoleDevice, CoverageConsole};
use crate::io::uart::Uart;

/// Base trait for middlewares that wrap an inner object.
pub trait Middleware {
    type Inner: ?Sized;
    fn inner(&self) -> &Self::Inner;
}

/// Interface for middlewares that wrap a console device.
pub trait ConsoleMiddleware: Middleware
where
    Self::Inner: ConsoleDevice,
{
    fn poll_read_impl(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        self.inner().poll_read(cx, buf)
    }

    fn write_impl(&self, buf: &[u8]) -> Result<()> {
        self.inner().write(buf)
    }

    fn as_coverage_console_impl(&self) -> Option<&dyn CoverageConsole> {
        self.inner().as_coverage_console()
    }
}

impl<T: ConsoleMiddleware> ConsoleDevice for T
where
    T::Inner: ConsoleDevice,
{
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        self.poll_read_impl(cx, buf)
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        self.write_impl(buf)
    }

    fn as_coverage_console(&self) -> Option<&dyn CoverageConsole> {
        self.as_coverage_console_impl()
    }
}

impl<T: ConsoleMiddleware> CoverageConsole for T
where
    T::Inner: CoverageConsole + ConsoleDevice,
{
    fn coverage_blocks_processed(&self) -> usize {
        self.inner().coverage_blocks_processed()
    }
}

/// Interface for middlewares that forward UART methods.
pub trait UartMiddleware: Middleware
where
    Self::Inner: Uart,
{
    fn get_baudrate_impl(&self) -> Result<u32> {
        self.inner().get_baudrate()
    }

    fn set_baudrate_impl(&self, baudrate: u32) -> Result<()> {
        self.inner().set_baudrate(baudrate)
    }

    fn get_flow_control_impl(&self) -> Result<crate::io::uart::FlowControl> {
        self.inner().get_flow_control()
    }

    fn set_flow_control_impl(&self, flow_control: bool) -> Result<()> {
        self.inner().set_flow_control(flow_control)
    }

    fn get_device_path_impl(&self) -> Result<String> {
        self.inner().get_device_path()
    }

    fn clear_rx_buffer_impl(&self) -> Result<()> {
        self.inner().clear_rx_buffer()
    }

    fn set_parity_impl(&self, parity: crate::io::uart::Parity) -> Result<()> {
        self.inner().set_parity(parity)
    }

    fn get_parity_impl(&self) -> Result<crate::io::uart::Parity> {
        self.inner().get_parity()
    }

    fn set_break_impl(&self, enable: bool) -> Result<()> {
        self.inner().set_break(enable)
    }

    fn borrow_fd_impl(&self) -> Result<std::os::fd::BorrowedFd<'_>> {
        self.inner().borrow_fd()
    }
}

impl<T: UartMiddleware> Uart for T
where
    T: ConsoleDevice,
    T::Inner: Uart,
{
    fn get_baudrate(&self) -> Result<u32> {
        self.get_baudrate_impl()
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.set_baudrate_impl(baudrate)
    }

    fn get_flow_control(&self) -> Result<crate::io::uart::FlowControl> {
        self.get_flow_control_impl()
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.set_flow_control_impl(flow_control)
    }

    fn get_device_path(&self) -> Result<String> {
        self.get_device_path_impl()
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        self.clear_rx_buffer_impl()
    }

    fn set_parity(&self, parity: crate::io::uart::Parity) -> Result<()> {
        self.set_parity_impl(parity)
    }

    fn get_parity(&self) -> Result<crate::io::uart::Parity> {
        self.get_parity_impl()
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        self.set_break_impl(enable)
    }

    fn borrow_fd(&self) -> Result<std::os::fd::BorrowedFd<'_>> {
        self.borrow_fd_impl()
    }
}

impl<T: ?Sized> Middleware for &T {
    type Inner = T;
    fn inner(&self) -> &T {
        self
    }
}
impl<T: ConsoleDevice + ?Sized> ConsoleMiddleware for &T {}
impl<T: crate::io::uart::Uart + ?Sized> UartMiddleware for &T {}

impl<T: ?Sized> Middleware for Rc<T> {
    type Inner = T;
    fn inner(&self) -> &T {
        self
    }
}
impl<T: ConsoleDevice + ?Sized> ConsoleMiddleware for Rc<T> {}
impl<T: crate::io::uart::Uart + ?Sized> UartMiddleware for Rc<T> {}

impl<T: ?Sized> Middleware for Box<T> {
    type Inner = T;
    fn inner(&self) -> &T {
        self
    }
}
impl<T: ConsoleDevice + ?Sized> ConsoleMiddleware for Box<T> {}
impl<T: crate::io::uart::Uart + ?Sized> UartMiddleware for Box<T> {}
