module {
  func.func @unused_arg(%arg0: memref<1xi32>, %arg1: memref<1xi32>, %arg2: i32) -> i32 {
    %c0 = arith.constant 0 : index
    %0 = memref.load %arg1[%c0] {handshake.name = "load0"} : memref<1xi32>
    return %0 : i32
  }
}
