//! Board file for LowRISC OpenTitan RISC-V development platform.
//!
//! - <https://opentitan.org/>

#![no_std]
#![no_main]
#![feature(asm)]

use tock::kernel;
use tock::capsules;
use tock::components;
use tock::rv32i;

use capsules::virtual_alarm::{MuxAlarm, VirtualMuxAlarm};
use kernel::capabilities;
use kernel::common::dynamic_deferred_call::{DynamicDeferredCall, DynamicDeferredCallClientState};
use kernel::component::Component;
use kernel::hil;
use kernel::Platform;
use kernel::{create_capability, debug, static_init};
use rv32i::csr;

mod counter_demo;

pub mod io;
//
// Actual memory for holding the active process structures. Need an empty list
// at least.
static mut PROCESSES: [Option<&'static dyn kernel::procs::ProcessType>; 4] =
    [None, None, None, None];

static mut CHIP:Option<&'static earlgrey::chip::Earlgrey> = None;

// How should the kernel respond when a process faults.
const FAULT_RESPONSE: kernel::procs::FaultResponse = kernel::procs::FaultResponse::Panic;

// RAM to be shared by all application processes.
#[link_section = ".app_memory"]
static mut APP_MEMORY: [u8; 8192] = [0; 8192];

// Force the emission of the `.apps` segment in the kernel elf image
// NOTE: This will cause the kernel to overwrite any existing apps when flashed!
#[used]
#[link_section = ".app.hack"]
static APP_HACK: u8 = 0;

/// Dummy buffer that causes the linker to reserve enough space for the stack.
#[no_mangle]
#[link_section = ".stack_buffer"]
pub static mut STACK_MEMORY: [u8; 0x1000] = [0; 0x1000];

static OT_SPLASH: &[&str] = &[

    "#######################################",
    "#######################################",
    "#                                     #",
    "# /////**///                  /**     #",
    "#     /**      ******   ***** /**  ** #",
    "#     /**     **////** **///**/** **  #",
    "#     /**    /**   /**/**  // /****   #",
    "#     /**    /**   /**/**   **/**/**  #",
    "#     /**    //****** //***** /**//** #",
    "#     //      //////   /////  //  //  #",
    "#                                     #",
    "#                                     #",
    "#            ******  *******          #",
    "#           **////**//**///**         #",
    "#          /**   /** /**  /**         #",
    "#          /**   /** /**  /**         #",
    "##        //******  ***  /**         ##",
    "#####      //////  ///   //       #####",
    "#######                         #######",
    "#######################################",
    "############`````#####`````############",
    "###########``````#####``````###########",
    "###########``````#####``````###########",
    "######````````````###````````````######",
    "######````````````###````````````######",
    "######````````````###````````````######",
    "#```````````###############```````````#",
    "#```````````##```````````##```````````#",
    "#```````````##```````````##```````````#",
    "##############```````````##############",
    "##############```````````##############",
    "#```````````##```````````##```````````#",
    "#```````````##```````````##```````````#",
    "#```````````###############```````````#",
    "######````````````###````````````######",
    "######````````````###````````````######",
    "######````````````###````````````######",
    "###########``````#####``````###########",
    "###########``````#####``````###########",
    "############`````#####`````############",
    "#######################################",
];

/// A structure representing this platform that holds references to all
/// capsules for this platform. We've included an alarm and console.
struct OpenTitan {
    console: &'static capsules::console::Console<'static>,
    alarm: &'static capsules::alarm::AlarmDriver<
        'static,
        VirtualMuxAlarm<'static, earlgrey::timer::RvTimer<'static>>,
    >,
}

/// Mapping of integer syscalls to objects that implement syscalls.
impl Platform for OpenTitan {
    fn with_driver<F, R>(&self, driver_num: usize, f: F) -> R
    where
        F: FnOnce(Option<&dyn kernel::Driver>) -> R,
    {
        match driver_num {
            capsules::console::DRIVER_NUM => f(Some(self.console)),
            capsules::alarm::DRIVER_NUM => f(Some(self.alarm)),
            _ => f(None),
        }
    }
}

/// Reset Handler.
///
/// This function is called from the arch crate after some very basic RISC-V
/// setup.
#[no_mangle]
pub unsafe fn reset_handler() {
    // Basic setup of the platform.
    rv32i::init_memory();
    // Earlgrey-specific handler
    earlgrey::chip::configure_trap_handler();

    // initialize capabilities
    let process_mgmt_cap = create_capability!(capabilities::ProcessManagementCapability);
    let memory_allocation_cap = create_capability!(capabilities::MemoryAllocationCapability);

    let main_loop_cap = create_capability!(capabilities::MainLoopCapability);

    let board_kernel = static_init!(kernel::Kernel, kernel::Kernel::new(&PROCESSES));

    let dynamic_deferred_call_clients =
        static_init!([DynamicDeferredCallClientState; 1], Default::default());
    let dynamic_deferred_caller = static_init!(
        DynamicDeferredCall,
        DynamicDeferredCall::new(dynamic_deferred_call_clients)
    );
    DynamicDeferredCall::set_global_instance(dynamic_deferred_caller);

    let chip = static_init!(earlgrey::chip::Earlgrey, earlgrey::chip::Earlgrey::new());
    CHIP = Some(chip);

    // Need to enable all interrupts for Tock Kernel
    chip.enable_plic_interrupts();
    // enable interrupts globally
    csr::CSR
        .mie
        .modify(csr::mie::mie::msoft::SET + csr::mie::mie::mtimer::SET + csr::mie::mie::mext::SET);
    csr::CSR.mstatus.modify(csr::mstatus::mstatus::mie::SET);

    // Create a shared UART channel for the console and for kernel debug.
    let uart_mux = components::console::UartMuxComponent::new(
        &earlgrey::uart::UART0,
        earlgrey::uart::UART0_BAUDRATE,
        dynamic_deferred_caller,
    )
    .finalize(());

    let alarm = &earlgrey::timer::TIMER;
    alarm.setup();

    // Create a shared virtualization mux layer on top of a single hardware
    // alarm.
    let mux_alarm = static_init!(
        MuxAlarm<'static, earlgrey::timer::RvTimer>,
        MuxAlarm::new(alarm)
    );
    hil::time::Alarm::set_client(&earlgrey::timer::TIMER, mux_alarm);

    // Alarm
    let virtual_alarm_user = static_init!(
        VirtualMuxAlarm<'static, earlgrey::timer::RvTimer>,
        VirtualMuxAlarm::new(mux_alarm)
    );
    let alarm = static_init!(
        capsules::alarm::AlarmDriver<'static, VirtualMuxAlarm<'static, earlgrey::timer::RvTimer>>,
        capsules::alarm::AlarmDriver::new(
            virtual_alarm_user,
            board_kernel.create_grant(&memory_allocation_cap)
        )
    );
    hil::time::Alarm::set_client(virtual_alarm_user, alarm);

    // Setup the console.
    let console = components::console::ConsoleComponent::new(board_kernel, uart_mux).finalize(());
    // Create the debugger object that handles calls to `debug!()`.
    components::debug_writer::DebugWriterComponent::new(uart_mux).finalize(());

    let counter_demo_mux = static_init!(
        capsules::virtual_alarm::VirtualMuxAlarm<'static, earlgrey::timer::RvTimer>,
        capsules::virtual_alarm::VirtualMuxAlarm::new(mux_alarm)
    );

    let pins = &[7, 8, 9, 10, 11, 12, 13, 14];
    for pin in pins {
        hil::gpio::Pin::make_output(&earlgrey::gpio::PORT[*pin]);
    }

    let counter_demo_inst = static_init!(
        counter_demo::CounterAlarm<'static, capsules::virtual_alarm::VirtualMuxAlarm<earlgrey::timer::RvTimer>>,
        counter_demo::CounterAlarm::new(counter_demo_mux, pins)
    );
    counter_demo_inst.add_splash_text(OT_SPLASH);

    hil::time::Alarm::set_client(counter_demo_mux, counter_demo_inst);

    counter_demo_inst.run(500);

    debug!("OpenTitan initialisation complete. Entering main loop");

    extern "C" {
        /// Beginning of the ROM region containing app images.
        ///
        /// This symbol is defined in the linker script.
        static _sapps: u8;
    }

    let opentitan = OpenTitan {
        console: console,
        alarm: alarm,
    };

    kernel::procs::load_processes(
        board_kernel,
        chip,
        &_sapps as *const u8,
        &mut APP_MEMORY,
        &mut PROCESSES,
        FAULT_RESPONSE,
        &process_mgmt_cap,
    );

    board_kernel.kernel_loop(&opentitan, chip, None, &main_loop_cap);
}
