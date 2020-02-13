//! Implementation of the physical memory protection unit (PMP).

use core::cmp;
use core::fmt::{Display, Formatter};
use core::iter::Take;
use core::marker::PhantomData;
use core::slice;

use crate::csr::CSR;
use kernel::mpu::{Permissions, Region, MPU};

const CFG_PROT_READ: u8 = 1 << 0;
const CFG_PROT_WRITE: u8 = 1 << 1;
const CFG_PROT_EXEC: u8 = 1 << 2;
const CFG_MODE_OFF: u8 = 0;
const CFG_MODE_TOR: u8 = 1 << 3;
const CFG_MODE_NA4: u8 = 2 << 3;
const CFG_MODE_NAPOT: u8 = 3 << 3;

/// Holds values to be stored in pmpcfg# and pmpaddr# to represent a PMP mapping
struct PMPEntry {
    cfg: u8,
    addr: usize,
}

/// Describes a memory region to be represented by PMP register value(s)
#[derive(Default, Clone, Copy)]
pub struct PMPRegion {
    addr: usize,
    size: usize,
    prot: u8,
    mode: u8,
}

fn perm_to_prot(perm: Permissions) -> u8 {
    match perm {
        Permissions::ReadWriteExecute => CFG_PROT_READ | CFG_PROT_WRITE | CFG_PROT_EXEC,
        Permissions::ReadWriteOnly => CFG_PROT_READ | CFG_PROT_WRITE,
        Permissions::ReadExecuteOnly => CFG_PROT_READ | CFG_PROT_EXEC,
        Permissions::ReadOnly => CFG_PROT_READ,
        Permissions::ExecuteOnly => CFG_PROT_EXEC,
    }
}

fn layout_to_mode(addr: usize, size: usize) -> u8 {
    if size == 4 {
        CFG_MODE_NA4
    } else if usize::is_power_of_two(size) && addr & (size - 1) == 0 {
        // Are `addr` and `size` region naturally aligned to a power of two?
        CFG_MODE_NAPOT
    } else {
        CFG_MODE_TOR
    }
}

impl PMPRegion {
    fn new(addr: usize, size: usize, perm: Permissions) -> Self {
        PMPRegion {
            addr,
            size,
            prot: perm_to_prot(perm),
            mode: layout_to_mode(addr, size),
        }
    }

    fn render(&self) -> (PMPEntry, Option<PMPEntry>) {
        if self.mode != CFG_MODE_TOR {
            let end = self.addr | (self.size - 1);
            (
                PMPEntry {
                    cfg: self.prot | self.mode,
                    addr: end >> 2,
                },
                None,
            )
        } else {
            let bor = PMPEntry {
                cfg: CFG_MODE_OFF,
                addr: self.addr >> 2,
            };

            let end = self.addr + self.size - 1;
            let tor = PMPEntry {
                cfg: self.prot | CFG_MODE_TOR,
                addr: end >> 2,
            };

            (bor, Some(tor))
        }
    }

    fn needed_regs(&self) -> u8 {
        match self.mode == CFG_MODE_TOR {
            true => 2,
            false => 1,
        }
    }

    fn overlaps(&self, other: &Self) -> bool {
        let other_addr = other.addr;
        let other_end = other.addr + other.size;

        if other_addr <= self.addr {
            other_end > self.addr
        } else {
            other_addr < (self.addr + self.size)
        }
    }

    fn set_perm(&mut self, perm: Permissions) {
        self.prot = perm_to_prot(perm);
    }
}

struct PMPConfig<'a> {
    regions: &'a mut [PMPRegion],
    nregions: &'a mut u8,
    max_cfg_registers: u8,
}

impl PMPConfig<'a> {
    pub fn new<'b>(
        regions: &'b mut [PMPRegion],
        nregions: &'b mut u8,
        max_cfg_registers: u8,
    ) -> Self
    where
        'b: 'a,
    {
        // TODO: validate slice length
        Self {
            regions,
            nregions,
            max_cfg_registers,
        }
    }

    pub fn render_iter<'b>(regions: &'b [PMPRegion], nregions: u8) -> Iter<'b> {
        Iter {
            region_iter: regions.iter().take(nregions as usize),
            tor: None,
        }
    }

    pub fn map(&mut self, addr: usize, size: usize, perm: Permissions) -> Option<()> {
        let new_region = PMPRegion::new(addr, size, perm);
        self.append(&new_region)
    }

    pub fn resize(&mut self, addr: usize, new_size: usize) -> Option<()> {
        let mut old_region = self.remove(addr)?;
        let old_size = old_region.size;
        old_region.size = new_size;
        if self.append(&old_region).is_none() {
            old_region.size = old_size;
            let undo = self.append(&old_region);
            assert!(undo.is_some());
            None
        } else {
            Some(())
        }
    }

    pub fn set_perm(&mut self, addr: usize, new_perm: Permissions) -> Option<()> {
        let ent = self.regions[0..*self.nregions as usize]
            .iter_mut()
            .find(|e| e.addr == addr)?;
        ent.set_perm(new_perm);
        Some(())
    }

    fn remove(&mut self, addr: usize) -> Option<PMPRegion> {
        let remove_idx = self
            .regions
            .iter()
            .take(*self.nregions as usize)
            .position(|e| e.addr == addr)?;
        *self.nregions -= 1;
        if remove_idx as u8 == *self.nregions {
            // Removing the tail is easy.
            // Decrementing `nregions` just shaved it off.
            Some(self.regions[remove_idx])
        } else {
            let res: PMPRegion = self.regions[remove_idx];
            // Copy the old tail into the newly made "hole"
            self.regions[remove_idx] = self.regions[*self.nregions as usize];
            Some(res)
        }
    }

    fn append(&mut self, new_region: &PMPRegion) -> Option<()> {
        if *self.nregions >= self.max_cfg_registers {
            return None;
        }

        // Ensure the new region does not overlap with any existing ones and will not push the
        // config over its pmpcfg register budget.
        let mut nregs = 0;
        for r in self.regions.iter().take(*self.nregions as usize) {
            if r.overlaps(new_region) {
                return None;
            }
            nregs += r.needed_regs();
        }
        if nregs + new_region.needed_regs() > self.max_cfg_registers {
            return None;
        }

        self.regions[*self.nregions as usize] = *new_region;
        *self.nregions += 1;
        Some(())
    }
}

struct Iter<'a> {
    region_iter: Take<slice::Iter<'a, PMPRegion>>,
    tor: Option<PMPEntry>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = PMPEntry;

    fn next(&mut self) -> Option<Self::Item> {
        let tor = self.tor.take();
        if tor.is_none() {
            match self.region_iter.next() {
                Some(region) => {
                    let (res, tor) = region.render();
                    self.tor = tor;
                    Some(res)
                }
                None => None,
            }
        } else {
            tor
        }
    }
}

/// Config implementation for fully capable (16 entry, 4-byte granularity) MPU
#[derive(Default)]
pub struct FullMPUConfig {
    regions: [PMPRegion; 16],
    nregions: u8,
    app_region: Option<(usize, usize)>,
}

impl Display for FullMPUConfig {
    fn fmt(&self, _f: &mut Formatter) -> core::fmt::Result {
        Ok(())
    }
}

impl RiscvMPUConfig for FullMPUConfig {
    fn state<'a>(&'a self) -> (&'a [PMPRegion], u8) {
        (&self.regions, self.nregions)
    }
    fn state_mut<'a>(&'a mut self) -> (&'a mut [PMPRegion], &'a mut u8) {
        (&mut self.regions, &mut self.nregions)
    }

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
        let mut cfgs = [0u32; 4];
        let mut addrs = [0u32; 16];

        self.render(&mut cfgs, &mut addrs);
        CSR.pmpcfg0.set(cfgs[0]);
        CSR.pmpcfg1.set(cfgs[1]);
        CSR.pmpcfg2.set(cfgs[2]);
        CSR.pmpcfg3.set(cfgs[3]);
        CSR.pmpaddr0.set(addrs[0]);
        CSR.pmpaddr1.set(addrs[1]);
        CSR.pmpaddr2.set(addrs[2]);
        CSR.pmpaddr3.set(addrs[3]);
        CSR.pmpaddr4.set(addrs[4]);
        CSR.pmpaddr5.set(addrs[5]);
        CSR.pmpaddr6.set(addrs[6]);
        CSR.pmpaddr7.set(addrs[7]);
        CSR.pmpaddr8.set(addrs[8]);
        CSR.pmpaddr9.set(addrs[9]);
        CSR.pmpaddr10.set(addrs[10]);
        CSR.pmpaddr11.set(addrs[11]);
        CSR.pmpaddr12.set(addrs[12]);
        CSR.pmpaddr13.set(addrs[13]);
        CSR.pmpaddr14.set(addrs[14]);
        CSR.pmpaddr15.set(addrs[15]);
    }

    fn max_regions() -> u8 {
        16u8
    }
    fn granularity() -> usize {
        4usize
    }
}

pub trait RiscvMPUConfig {
    fn set_app_region(&mut self, addr: usize, size: usize) -> Option<()>;
    fn get_app_region(&self) -> Option<(usize, usize)>;
    fn apply(&self);
    fn max_regions() -> u8;
    fn granularity() -> usize;

    fn state<'a>(&'a self) -> (&'a [PMPRegion], u8);
    fn state_mut<'a>(&'a mut self) -> (&'a mut [PMPRegion], &'a mut u8);

    fn map(&mut self, addr: usize, size: usize, perm: Permissions) -> Option<()> {
        Self::valid_mapping(addr, size)?;

        let (regions, nregions) = self.state_mut();
        let mut cfg = PMPConfig::new(regions, nregions, Self::max_regions());
        cfg.map(addr, size, perm)
    }

    fn resize(&mut self, addr: usize, new_size: usize) -> Option<()> {
        Self::valid_mapping(addr, new_size)?;

        let (regions, nregions) = self.state_mut();
        let mut cfg = PMPConfig::new(regions, nregions, Self::max_regions());
        cfg.resize(addr, new_size)
    }

    fn set_perm(&mut self, addr: usize, perm: Permissions) -> Option<()> {
        let (regions, nregions) = self.state_mut();
        let mut cfg = PMPConfig::new(regions, nregions, Self::max_regions());
        cfg.set_perm(addr, perm)
    }

    fn render(&self, cfgs: &mut [u32], addrs: &mut [u32]) {
        let (regions, nregions) = self.state();
        let iter = PMPConfig::render_iter(regions, nregions);
        for (idx, entry) in iter.enumerate() {
            let cfg_reg = idx / 4; /* 0-3 -> pmpcfg0-pmpcfg3 */
            let cfg_field = idx % 4; /* fields 0-3 in pmpcfg# */
            let cfg_shift = cfg_field * 8;

            cfgs[cfg_reg] |= u32::from(entry.cfg) << cfg_shift;
            addrs[idx] = entry.addr as u32;
        }
    }

    fn valid_mapping(size: usize, addr: usize) -> Option<()> {
        let end = addr.checked_add(size)?;
        let granularity = Self::granularity();
        debug_assert!(usize::is_power_of_two(granularity));
        let mask = granularity - 1;

        if size == 0 || addr & mask != 0 || end & mask != 0 {
            None
        } else {
            Some(())
        }
    }

    fn round_to_granularity(addr: usize) -> usize {
        let granularity = Self::granularity();
        debug_assert!(usize::is_power_of_two(granularity));
        let mask = granularity - 1;
        (addr + mask) & !mask
    }
}

pub struct RiscvMPU<T> {
    phantom: PhantomData<T>,
}

impl<T> RiscvMPU<T>
where
    T: RiscvMPUConfig + Display + Default,
{
    pub fn new() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<T> MPU for RiscvMPU<T>
where
    T: RiscvMPUConfig + Display + Default,
{
    type MpuConfig = T;

    fn enable_mpu(&self) {
        // PMP enforcement is enabled on entry to U-mode
    }

    fn disable_mpu(&self) {
        // PMP enforcement is disabled on entry to M-mode
    }

    fn number_total_regions(&self) -> usize {
        Self::MpuConfig::max_regions() as usize
    }

    fn allocate_region(
        &self,
        unallocated_memory_start: *const u8,
        unallocated_memory_size: usize,
        min_region_size: usize,
        permissions: Permissions,
        config: &mut Self::MpuConfig,
    ) -> Option<Region> {
        if unallocated_memory_size == min_region_size {
            let addr = unallocated_memory_start as usize;
            let size = min_region_size;

            // no choice about placement since the size is exact
            if config.map(addr, size, permissions).is_some() {
                return Some(Region::new(addr as *const u8, size));
            } else {
                None
            }
        } else {
            // TODO: do better alignment?
            None
        }
    }

    fn allocate_app_memory_region(
        &self,
        unallocated_memory_start: *const u8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        permissions: Permissions,
        config: &mut Self::MpuConfig,
    ) -> Option<(*const u8, usize)> {
        if config.get_app_region().is_some() {
            // app region already exists
            return None;
        }
        // XXX: better overflow handling
        let base_addr = unallocated_memory_start as usize;
        // ensure that the region is properly aligned
        let start_addr = Self::MpuConfig::round_to_granularity(base_addr);

        // Make sure there is enough memory for app memory and kernel memory.
        let memory_size = Self::MpuConfig::round_to_granularity(cmp::max(
            min_memory_size,
            initial_app_memory_size + initial_kernel_memory_size,
        ));

        let end_addr = start_addr + memory_size;
        let padded_size = base_addr - end_addr;

        if padded_size > unallocated_memory_size {
            return None;
        }
        if config.map(start_addr, memory_size, permissions).is_some() {
            assert!(config.set_app_region(start_addr, memory_size).is_some());
            Some((start_addr as *const u8, memory_size))
        } else {
            None
        }
    }

    fn update_app_memory_region(
        &self,
        app_memory_break: *const u8,
        kernel_memory_break: *const u8,
        permissions: Permissions,
        config: &mut Self::MpuConfig,
    ) -> Result<(), ()> {
        let app_brk = app_memory_break as usize;
        let kernel_brk = kernel_memory_break as usize;
        let (app_base, app_size) = config.get_app_region().ok_or(())?;

        // Do not allow any of the following conditions
        // 1. App heap shrinking beyond nothing
        // 2. App heap extending into kernel grant space
        // 3. Kernel grant space shrinking beyond nothing
        if app_brk < app_base || app_brk > kernel_brk || kernel_brk > app_base + app_size {
            return Err(());
        }

        if config.resize(app_base, app_brk - app_base).is_some() {
            let _ = config.set_perm(app_base, permissions);
            Ok(())
        } else {
            Err(())
        }
    }

    fn configure_mpu(&self, config: &Self::MpuConfig) {
        config.apply();
    }
}
