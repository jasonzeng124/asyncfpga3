module {
  func.func @simple_example_1(%arg0: memref<100xi32>) {
    %c100_i32 = arith.constant 100 : i32
    %c0 = arith.constant 0 : index
    memref.store %c100_i32, %arg0[%c0] {handshake.name = "store0"} : memref<100xi32>
    return
  }
}
