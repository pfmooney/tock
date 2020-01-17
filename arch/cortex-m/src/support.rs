use core::ops::FnOnce;

#[cfg(all(target_arch = "arm", target_os = "none"))]
#[inline(always)]
/// NOP instruction
pub fn nop() {
    unsafe {
        asm!("nop" :::: "volatile");
    }
}

#[cfg(all(target_arch = "arm", target_os = "none"))]
#[inline(always)]
/// WFI instruction
pub unsafe fn wfi() {
    asm!("wfi" :::: "volatile");
}

#[cfg(all(target_arch = "arm", target_os = "none"))]
pub unsafe fn atomic<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    // Set PRIMASK
    asm!("cpsid i" :::: "volatile");

    let res = f();

    // Unset PRIMASK
    asm!("cpsie i" :::: "volatile");
    return res;
}

#[cfg(all(target_arch = "arm", target_os = "none"))]
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {}

// Mock implementations for tests on Travis-CI.
#[cfg(not(any(target_arch = "arm", target_os = "none")))]
/// NOP instruction (mock)
pub fn nop() {
    unimplemented!()
}

#[cfg(not(any(target_arch = "arm", target_os = "none")))]
/// WFI instruction (mock)
pub unsafe fn wfi() {
    unimplemented!()
}

#[cfg(not(any(target_arch = "arm", target_os = "none")))]
pub unsafe fn atomic<F, R>(_f: F) -> R
where
    F: FnOnce() -> R,
{
    unimplemented!()
}

#[cfg(all(target_arch = "arm", target_os = "none"))]
pub fn panic_quiesce() {
    // Let any outstanding uart DMAs finish
    for _ in 0..200000 {
        nop();
    }
}
