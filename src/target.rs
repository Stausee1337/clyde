use std::str::FromStr;

use inkwell::targets::{self as ll, TargetTriple};

use crate::type_ir::{Align, Endianness, Size};

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub struct TargetDataLayout {
    pub endian: Endianness,

    pub i8_align: Align,
    pub i16_align: Align,
    pub i32_align: Align,
    pub i64_align: Align,

    pub f32_align: Align,
    pub f64_align: Align,

    pub ptr_size: Size,
    pub ptr_align: Align,
}

impl Default for TargetDataLayout {
    fn default() -> Self {
        Self {
            endian: Endianness::Little,
            i8_align: Align::from_bits(8),
            i16_align: Align::from_bits(16),
            i32_align: Align::from_bits(32),
            i64_align: Align::from_bits(64),

            f32_align: Align::from_bits(32),
            f64_align: Align::from_bits(64),

            ptr_size: Size::from_bits(64),
            ptr_align: Align::from_bits(64),
        }
    }
}

impl TargetDataLayout {
    fn parse_from_llvm_str(layout: &str) -> Result<Self, ()> {
        let mut this = TargetDataLayout::default();
        let specs = layout.split('-');

        macro_rules! match_from_size {
            (int $size:expr) => {
                match $size.in_bytes {
                    1 => &mut this.i8_align,
                    2 => &mut this.i16_align,
                    4 => &mut this.i32_align,
                    8 => &mut this.i64_align,
                    _ => continue // ignore other sizes
                }
            };
            (float $size:expr) => {
                match $size.in_bytes {
                    4 => &mut this.f32_align,
                    8 => &mut this.f64_align,
                    _ => continue // ignore other sizes
                }
            }
        }

        macro_rules! u64_from_str {
            ($expr:expr) =>  { u64::from_str($expr).map_err(|_| ()) }
        }

        fn parse_llvm_align(abi: &str) -> Result<Align, ()> {
            let abi = u64_from_str!(abi)?;
            Ok(Align::from_bits(abi))
        }

        for spec in specs {
            let comps = spec.split(':').collect::<Vec<_>>();
            match *comps {
                ["e", ..] => this.endian = Endianness::Little,
                ["E", ..] => this.endian = Endianness::Big,
                ["p", size, abi] => {
                    let size = u64_from_str!(size)?;
                    let size = Size::from_bits(size);

                    let align = parse_llvm_align(abi)?;
                    this.ptr_size = size;
                    this.ptr_align = align;
                }
                [i, abi] if i.starts_with("i") => {
                    let size = u64::from_str(&i[1..]).map_err(|_| ())?;
                    let size = Size::from_bits(size);

                    let align = parse_llvm_align(abi)?;

                    *match_from_size!(int size) = align; 
                }
                [f, abi] if f.starts_with("f") => {
                    let size = u64::from_str(&f[1..]).map_err(|_| ())?;
                    let size = Size::from_bits(size);

                    let align = parse_llvm_align(abi)?;

                    *match_from_size!(float size) = align; 
                }
                _ => ()
            }
        }

        Ok(this)
    }
}

pub trait DataLayoutExt {
    fn data_layout(&self) -> &TargetDataLayout;
}

#[allow(dead_code)]
pub struct Target {
    pub triple: TargetTriple,
    llvm_target: ll::Target,
    llvm_target_machine: ll::TargetMachine,
    data_layout: TargetDataLayout
}

impl Target {
    // FIXME: the host Target doesn't always need to be an x86, set this information during
    // compile time and read here
    pub fn host() -> Option<Self> { 
        ll::Target::initialize_x86(&inkwell::targets::InitializationConfig::default());
        let triple = ll::TargetMachine::get_default_triple();
        let target = ll::Target::from_triple(&triple)
            .map_err(|msg |{
                eprintln!("ERROR: Could not build llvm target: {}", msg.to_bytes().escape_ascii());
            })
            .ok()?;
        let machine = target.create_target_machine_from_options(&triple, inkwell::targets::TargetMachineOptions::default())
            .ok_or(())
            .map_err(|_| {
                eprintln!("ERROR: Could not build llvm target");
            })
            .ok()?;
        let data_layout = machine.get_target_data().get_data_layout();
        let layout_string = data_layout.as_str();
        let layout_string = layout_string.to_str()
            .map_err(|_| {
                eprintln!("ERROR: Could not build llvm target: invalid data layout");
            })
            .ok()?;

        let data_layout = TargetDataLayout::parse_from_llvm_str(layout_string)
            .map_err(|_| {
                eprintln!("ERROR: Could not build llvm target: invalid data layout");
            })
            .ok()?;

        Some(Self {
            triple,
            llvm_target: target,
            llvm_target_machine: machine,
            data_layout
        })
    }

    pub fn get_llvm_target_machine(&self) -> &ll::TargetMachine {
        &self.llvm_target_machine
    }

    // TODO: add `search` here to try and create targets from triple str
}

impl DataLayoutExt for Target {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.data_layout
    }
}

