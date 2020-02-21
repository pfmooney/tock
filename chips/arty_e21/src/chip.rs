use core::fmt::{Write, Display, Formatter};
use kernel;
use kernel::debug;
use rv32i;
use rv32i::csr::CSR;
use rv32i::pmp::{RiscvMPU, RiscvMPUConfig, PMPRegion};

use crate::gpio;
use crate::interrupts;
use crate::timer;
use crate::uart;

extern "C" {
    fn _start_trap();
}

#[derive(Default)]
pub struct E21MPUConfig {
    regions: [PMPRegion; 4],
    nregions: u8,
    app_region: Option<(usize, usize)>,
}

impl RiscvMPUConfig for E21MPUConfig {
    fn set_app_region(&mut self, addr: usize, size: usize) -> Option<()> {
        if self.app_region.is_some() {
            None
        } else {
            self.app_region = Some((addr, size));
            Some(())
        }
    }

    fn get_app_region(&self) -> Option<(usize, usize)> {
        self.app_region
    }

    fn apply(&self) {
        let mut cfgs = [0u32; 1];
        let mut addrs = [0u32; 4];
        self.render(&mut cfgs, &mut addrs);

        CSR.pmpcfg0.set(cfgs[0]);
        CSR.pmpaddr0.set(addrs[0]);
        CSR.pmpaddr1.set(addrs[1]);
        CSR.pmpaddr2.set(addrs[2]);
        CSR.pmpaddr3.set(addrs[3]);
    }

    // From the DS: "The E2 PMP unit has 4 regions and a minimum granularity of 4 bytes"
    fn max_regions() -> u8 {
        4u8
    }
    fn granularity() -> usize {
        4usize
    }

    fn state<'a>(&'a self) -> (&'a [PMPRegion], u8) {
        (&self.regions, self.nregions)
    }

    fn state_mut<'a>(&'a mut self) -> (&'a mut [PMPRegion], &'a mut u8) {
        (&mut self.regions, &mut self.nregions)
    }
}

impl Display for E21MPUConfig {
    fn fmt(&self, _f: &mut Formatter) -> core::fmt::Result {
        Ok(())
    }
}

pub struct ArtyExx {
    pmp: RiscvMPU<E21MPUConfig>,
    userspace_kernel_boundary: rv32i::syscall::SysCall,
    clic: rv32i::clic::Clic,
}

impl ArtyExx {
    pub unsafe fn new() -> ArtyExx {
        // Make a bit-vector of all interrupt locations that we actually intend
        // to use on this chip.
        // 0001 1111 1111 1111 1111 0000 0000 1000 0000
        let in_use_interrupts: u64 = 0x1FFFF0080;

        ArtyExx {
            pmp: RiscvMPU::new(),
            userspace_kernel_boundary: rv32i::syscall::SysCall::new(),
            clic: rv32i::clic::Clic::new(in_use_interrupts),
        }
    }

    pub fn enable_all_interrupts(&self) {
        self.clic.enable_all();
    }

    /// By default the machine timer is enabled and will trigger interrupts. To
    /// prevent that we can make the compare register very large to effectively
    /// stop the interrupt from triggering, and then the machine timer can be
    /// used later as needed.
    #[cfg(all(target_arch = "riscv32", target_os = "none"))]
    pub unsafe fn disable_machine_timer(&self) {
        asm!("
            // Initialize machine timer mtimecmp to disable the machine timer
            // interrupt.
            li   t0, -1       // Set mtimecmp to 0xFFFFFFFF
            lui  t1, %hi(0x02004000)     // Load the address of mtimecmp to t1
            addi t1, t1, %lo(0x02004000) // Load the address of mtimecmp to t1
            sw   t0, 0(t1)    // mtimecmp is 64 bits, set to all ones
            sw   t0, 4(t1)    // mtimecmp is 64 bits, set to all ones
        "
        :
        :
        :
        : "volatile");
    }

    // Mock implementation for tests on Travis-CI.
    #[cfg(not(any(target_arch = "riscv32", target_os = "none")))]
    pub unsafe fn disable_machine_timer(&self) {
        unimplemented!()
    }

    /// Setup the function that should run when a trap happens.
    ///
    /// This needs to be chip specific because how the CLIC works is configured
    /// when the trap handler address is specified in mtvec, and that is only
    /// valid for platforms with a CLIC.
    #[cfg(all(target_arch = "riscv32", target_os = "none"))]
    pub unsafe fn configure_trap_handler(&self) {
        asm!("
            // The csrw instruction writes a Control and Status Register (CSR)
            // with a new value.
            //
            // CSR 0x305 (mtvec, 'Machine trap-handler base address.') sets the
            // address of the trap handler. We do not care about its old value,
            // so we don't bother reading it. We want to enable direct CLIC mode
            // so we set the second lowest bit.
            lui  t0, %hi(_start_trap)
            addi t0, t0, %lo(_start_trap)
            ori  t0, t0, 0x02 // Set CLIC direct mode
            csrw 0x305, t0    // Write the mtvec CSR.
        "
        :
        :
        :
        : "volatile");
    }

    // Mock implementation for tests on Travis-CI.
    #[cfg(not(any(target_arch = "riscv32", target_os = "none")))]
    pub unsafe fn configure_trap_handler(&self) {
        unimplemented!()
    }

    /// Generic helper initialize function to setup all of the chip specific
    /// operations. Different boards can call the functions that `initialize()`
    /// calls directly if it needs to use a custom setup operation.
    pub unsafe fn initialize(&self) {
        self.disable_machine_timer();
        self.configure_trap_handler();
    }
}

impl kernel::Chip for ArtyExx {
    type MPU = RiscvMPU<E21MPUConfig>;
    type UserspaceKernelBoundary = rv32i::syscall::SysCall;
    type SysTick = ();

    fn mpu(&self) -> &Self::MPU {
        &self.pmp
    }

    fn systick(&self) -> &Self::SysTick {
        &()
    }

    fn userspace_kernel_boundary(&self) -> &rv32i::syscall::SysCall {
        &self.userspace_kernel_boundary
    }

    fn service_pending_interrupts(&self) {
        unsafe {
            while let Some(interrupt) = self.clic.next_pending() {
                match interrupt {
                    interrupts::MTIP => timer::MACHINETIMER.handle_interrupt(),

                    interrupts::GPIO0 => gpio::PORT[3].handle_interrupt(),
                    interrupts::GPIO1 => gpio::PORT[3].handle_interrupt(),
                    interrupts::GPIO2 => gpio::PORT[3].handle_interrupt(),
                    interrupts::GPIO3 => gpio::PORT[3].handle_interrupt(),
                    interrupts::GPIO4 => gpio::PORT[4].handle_interrupt(),
                    interrupts::GPIO5 => gpio::PORT[5].handle_interrupt(),
                    interrupts::GPIO6 => gpio::PORT[6].handle_interrupt(),
                    interrupts::GPIO7 => gpio::PORT[7].handle_interrupt(),
                    interrupts::GPIO8 => gpio::PORT[8].handle_interrupt(),
                    interrupts::GPIO9 => gpio::PORT[9].handle_interrupt(),
                    interrupts::GPIO10 => gpio::PORT[10].handle_interrupt(),
                    interrupts::GPIO11 => gpio::PORT[11].handle_interrupt(),
                    interrupts::GPIO12 => gpio::PORT[12].handle_interrupt(),
                    interrupts::GPIO13 => gpio::PORT[13].handle_interrupt(),
                    interrupts::GPIO14 => gpio::PORT[14].handle_interrupt(),
                    interrupts::GPIO15 => gpio::PORT[15].handle_interrupt(),

                    interrupts::UART0 => uart::UART0.handle_interrupt(),

                    _ => debug!("Pidx {}", interrupt),
                }

                // Mark that we are done with this interrupt and the hardware
                // can clear it.
                self.clic.complete(interrupt);
            }
        }
    }

    fn has_pending_interrupts(&self) -> bool {
        self.clic.has_pending()
    }

    fn sleep(&self) {
        unsafe {
            rv32i::support::wfi();
        }
    }

    unsafe fn atomic<F, R>(&self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        rv32i::support::atomic(f)
    }

    unsafe fn print_state(&self, write: &mut dyn Write) {
        rv32i::print_riscv_state(write);
    }
}

/// Trap handler for board/chip specific code.
///
/// For the arty-e21 this gets called when an interrupt occurs while the chip is
/// in kernel mode. All we need to do is check which interrupt occurred and
/// disable it.
#[cfg(all(target_arch = "riscv32", target_os = "none"))]
#[export_name = "_start_trap_rust"]
pub extern "C" fn start_trap_rust() {
    let mut mcause: i32;

    unsafe {
        asm!("
            // Read the mcause CSR to determine why we entered the trap handler.
            // Since we are using the CLIC, the hardware includes the interrupt
            // index in the mcause register.
            csrr $0, 0x342    // CSR=0x342=mcause
        "
        : "=r"(mcause)
        :
        :
        : "volatile");
    }

    // Check if the trap was from an interrupt or some other exception.
    if mcause < 0 {
        // If the most significant bit is set (i.e. mcause is negative) then
        // this was an interrupt. The interrupt number is then the lowest 8
        // bits.
        let interrupt_index = mcause & 0xFF;
        unsafe {
            rv32i::clic::disable_interrupt(interrupt_index as u32);
        }
    } else {
        // Otherwise, the kernel encountered a fault...so panic!()?
        panic!("kernel exception");
    }
}

/// Function that gets called if an interrupt occurs while an app was running.
/// mcause is passed in, and this function should correctly handle disabling the
/// interrupt that fired so that it does not trigger again.
#[export_name = "_disable_interrupt_trap_handler"]
pub extern "C" fn disable_interrupt_trap_handler(mcause: u32) {
    // The interrupt number is then the lowest 8
    // bits.
    let interrupt_index = mcause & 0xFF;
    unsafe {
        rv32i::clic::disable_interrupt(interrupt_index as u32);
    }
}
