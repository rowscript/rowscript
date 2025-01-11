macro_rules! entry {
    ($filename:literal) => {
        (concat!("(prelude) ", $filename), include_str!($filename))
    };
}

pub const FILES: [(&str, &str); 10] = [
    // Order-sensitive files.
    entry!("type.rows"),
    entry!("builtin.rows"),
    entry!("collection.rows"),
    entry!("op.rows"),
    entry!("reflect.rows"),
    // Order-insensitive files.
    entry!("console.rows"),
    entry!("effect.rows"),
    entry!("json.rows"),
    entry!("string.rows"),
    entry!("time.rows"),
];
