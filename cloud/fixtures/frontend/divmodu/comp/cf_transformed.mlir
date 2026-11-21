module {
  func.func @divmodu(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "b"}) -> i32 {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %0 = arith.divui %arg0, %arg1 {handshake.name = "divui0"} : i32
    %1 = arith.muli %0, %arg1 {handshake.name = "muli0"} : i32
    %2 = arith.subi %arg0, %1 {handshake.name = "subi0"} : i32
    %3 = arith.shli %2, %c1_i32 {handshake.name = "shli0"} : i32
    %4 = arith.addi %0, %3 {handshake.name = "addi0"} : i32
    return {handshake.name = "return0"} %4 : i32
  }
}

