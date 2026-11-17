module {
  func.func @twoloops(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%arg0, %c0_i32 : i32, i32), ^bb2(%arg0 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant6"} 1 : i32
    %c7_i32 = arith.constant {handshake.name = "constant7"} 7 : i32
    %3 = arith.shli %1, %c7_i32 {handshake.name = "shli0"} : i32
    %4 = arith.xori %1, %3 {handshake.name = "xori0"} : i32
    %5 = arith.addi %4, %2 {handshake.name = "addi0"} : i32
    %6 = arith.addi %2, %c1_i32 {handshake.name = "addi1"} : i32
    %7 = arith.cmpi slt, %6, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %7, ^bb1(%5, %6 : i32, i32), ^bb2(%5 : i32) {handshake.name = "cond_br1"}
  ^bb2(%8: i32):  // 2 preds: ^bb0, ^bb1
    %c255_i32 = arith.constant {handshake.name = "constant8"} 255 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant9"} 0 : i32
    %9 = arith.andi %8, %c255_i32 {handshake.name = "andi0"} : i32
    %10 = arith.cmpi ugt, %9, %c0_i32_0 {handshake.name = "cmpi2"} : i32
    cf.cond_br %10, ^bb3(%c0_i32_0, %8 : i32, i32), ^bb4(%8 : i32) {handshake.name = "cond_br2"}
  ^bb3(%11: i32, %12: i32):  // 2 preds: ^bb2, ^bb3
    %c40503_i32 = arith.constant {handshake.name = "constant10"} 40503 : i32
    %c3_i32 = arith.constant {handshake.name = "constant11"} 3 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant12"} 1 : i32
    %13 = arith.shrui %12, %c3_i32 {handshake.name = "shrui0"} : i32
    %14 = arith.xori %12, %13 {handshake.name = "xori1"} : i32
    %15 = arith.addi %14, %c40503_i32 {handshake.name = "addi2"} : i32
    %16 = arith.addi %11, %c1_i32_1 {handshake.name = "addi3"} : i32
    %17 = arith.cmpi ult, %16, %9 {handshake.name = "cmpi3"} : i32
    cf.cond_br %17, ^bb3(%16, %15 : i32, i32), ^bb4(%15 : i32) {handshake.name = "cond_br3"}
  ^bb4(%18: i32):  // 2 preds: ^bb2, ^bb3
    return {handshake.name = "return0"} %18 : i32
  }
}

