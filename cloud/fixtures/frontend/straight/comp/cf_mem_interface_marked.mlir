module {
  func.func @straight(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "b"}) -> i32 {
    %c7_i32 = arith.constant {handshake.name = "constant0"} 7 : i32
    %c3_i32 = arith.constant {handshake.name = "constant1"} 3 : i32
    %c2_i32 = arith.constant {handshake.name = "constant2"} 2 : i32
    %c11_i32 = arith.constant {handshake.name = "constant3"} 11 : i32
    %c-1640531527_i32 = arith.constant {handshake.name = "constant4"} -1640531527 : i32
    %0 = arith.addi %arg0, %arg1 {handshake.name = "addi0"} : i32
    %1 = arith.subi %arg0, %arg1 {handshake.name = "subi0"} : i32
    %2 = arith.shli %1, %c7_i32 {handshake.name = "shli0"} : i32
    %3 = arith.xori %0, %2 {handshake.name = "xori0"} : i32
    %4 = arith.shrui %arg0, %c3_i32 {handshake.name = "shrui0"} : i32
    %5 = arith.addi %3, %4 {handshake.name = "addi1"} : i32
    %6 = arith.shli %arg1, %c2_i32 {handshake.name = "shli1"} : i32
    %7 = arith.subi %5, %6 {handshake.name = "subi1"} : i32
    %8 = arith.shrui %7, %c11_i32 {handshake.name = "shrui1"} : i32
    %9 = arith.xori %7, %8 {handshake.name = "xori1"} : i32
    %10 = arith.addi %9, %c-1640531527_i32 {handshake.name = "addi2"} : i32
    %11 = arith.andi %0, %1 {handshake.name = "andi0"} : i32
    %12 = arith.subi %10, %11 {handshake.name = "subi2"} : i32
    %13 = arith.ori %arg0, %arg1 {handshake.name = "ori0"} : i32
    %14 = arith.addi %12, %13 {handshake.name = "addi3"} : i32
    return {handshake.name = "return0"} %14 : i32
  }
}

