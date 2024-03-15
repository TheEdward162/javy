use anyhow::Result;
use std::io::{Read, Write};

use javy::Runtime;

use crate::{APIConfig, JSApiSet};

pub(super) struct StreamIO;

impl JSApiSet for StreamIO {
    fn register(&self, runtime: &Runtime, _config: &APIConfig) -> Result<()> {
        let context = runtime.context();
        let global = context.global_object()?;

        let mut javy_object = global.get_property("Javy")?;
        if javy_object.type_of() == javy::quickjs::JSValueType::Undefined {
            javy_object = context.object_value()?;
            global.set_property("Javy", javy_object)?;
        }

        global.set_property(
            "__javy_io_writeSync",
            context.wrap_callback(|_, _this_arg, args| {
                let [fd, data, offset, length, ..] = args else {
                    anyhow::bail!("Invalid number of parameters");
                };

                let mut fd: Box<dyn Write> = match fd.try_into()? {
                    1u64 => Box::new(std::io::stdout()),
                    2 => Box::new(std::io::stderr()),
                    _ => anyhow::bail!("Only stdout and stderr are supported"),
                };
                let data: &[u8] = data.try_into()?;
                let offset: usize = offset.try_into()?;
                let length: usize = length.try_into()?;
                let data = &data[offset..(offset + length)];
                let n = fd.write(data)?;
                fd.flush()?;
                Ok(n.into())
            })?,
        )?;

        global.set_property(
            "__javy_io_readSync",
            context.wrap_callback(|_, _this_arg, args| {
                let [fd, data, offset, length, ..] = args else {
                    anyhow::bail!("Invalid number of parameters");
                };
                let mut fd: Box<dyn Read> = match fd.try_into()? {
                    0u64 => Box::new(std::io::stdin()),
                    _ => anyhow::bail!("Only stdin is supported"),
                };
                let offset: usize = offset.try_into()?;
                let length: usize = length.try_into()?;
                if data.type_of() != javy::quickjs::JSValueType::ArrayBuffer {
                    anyhow::bail!("Data needs to be an ArrayBuffer");
                }
                let data: &mut [u8] = data.try_into()?;
                let data = &mut data[offset..(offset + length)];
                let n = fd.read(data)?;
                Ok(n.into())
            })?,
        )?;

        context.eval_global("io.js", include_str!("io.js"))?;
        Ok(())
    }
}
