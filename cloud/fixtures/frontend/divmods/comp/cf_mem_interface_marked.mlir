module {
  func.func @divmods(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "b"}) -> i32 {
    %0 = arith.divsi %arg0, %arg1 {handshake.name = "divsi0"} : i32
    %1 = arith.remsi %arg0, %arg1 {handshake.name = "remsi0"} : i32
    %2 = arith.xori %0, %1 {handshake.name = "xori0"} : i32
    return {handshake.name = "return0"} %2 : i32
  }
}

