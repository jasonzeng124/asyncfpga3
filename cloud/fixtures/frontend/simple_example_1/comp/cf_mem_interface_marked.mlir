module {
  func.func @simple_example_1(%arg0: memref<100xi32> {handshake.arg_name = "a"}) {
    %c100_i32 = arith.constant {handshake.name = "constant0"} 100 : i32
    %c0 = arith.constant {handshake.name = "constant1"} 0 : index
    memref.store %c100_i32, %arg0[%c0] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store0"} : memref<100xi32>
    return {handshake.name = "return0"}
  }
}

