
#[repr(u32)]
pub enum Primitive {
    Bool, Void,
    SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint,
    Char, String
}

pub struct AdtDefInner {
    
}

pub enum TyKind {
    Primitive(Primitive),
    Adt()
}

