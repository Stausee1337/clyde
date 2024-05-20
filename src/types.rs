
#[repr(u32)]
pub enum Primitive {
    Bool, Void,
    SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint,
    String
}


pub enum Ty {
    Primitive(Primitive),
    Adt()
}

