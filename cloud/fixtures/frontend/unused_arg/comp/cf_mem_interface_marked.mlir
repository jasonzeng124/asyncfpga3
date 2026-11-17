module {
  func.func @unused_arg(%arg0: memref<1xi32> {handshake.arg_name = "a"}, %arg1: memref<1xi32> {handshake.arg_name = "used"}, %arg2: i32 {handshake.arg_name = "b"}) -> i32 {
    %c0 = arith.constant {handshake.name = "constant0"} 0 : index
    %0 = memref.load %arg1[%c0] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<1xi32>
    return {handshake.name = "return0"} %0 : i32
  }
}

