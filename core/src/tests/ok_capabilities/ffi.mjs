export function connectMySQL(dsn) {
    console.log("Connecting to:", dsn)
    return dsn
}

export function closeMySQL(conn) {
    console.log("Closing:", conn)
}
