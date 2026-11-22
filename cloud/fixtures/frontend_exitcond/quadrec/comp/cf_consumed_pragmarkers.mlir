module {
  func.func @quadrec(%arg0: i32 {handshake.arg_name = "x"}, %arg1: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c1013904242_i32 = arith.constant {handshake.name = "constant1"} 1013904242 : i32
    %c1779033703_i32 = arith.constant {handshake.name = "constant2"} 1779033703 : i32
    %c-1150833019_i32 = arith.constant {handshake.name = "constant3"} -1150833019 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c1013904242_i32, %arg0, %c1779033703_i32, %c-1150833019_i32 : i32, i32, i32, i32, i32), ^bb2(%c-1150833019_i32, %c1779033703_i32, %arg0, %c1013904242_i32 : i32, i32, i32, i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32, %3: i32, %4: i32, %5: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c3_i32 = arith.constant {handshake.name = "constant8"} 3 : i32
    %6 = arith.xori %4, %5 {handshake.name = "xori0"} : i32
    %7 = arith.addi %3, %6 {handshake.name = "addi0"} : i32
    %8 = arith.shrui %2, %c3_i32 {handshake.name = "shrui0"} : i32
    %9 = arith.addi %7, %8 {handshake.name = "addi1"} : i32
    %10 = arith.addi %1, %c1_i32 {handshake.name = "addi2"} : i32
    %11 = arith.cmpi ne, %10, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %11, ^bb1(%10, %9, %4, %5, %2 : i32, i32, i32, i32, i32), ^bb2(%2, %5, %4, %9 : i32, i32, i32, i32) {handshake.name = "cond_br1"}
  ^bb2(%12: i32, %13: i32, %14: i32, %15: i32):  // 2 preds: ^bb0, ^bb1
    %c2_i32 = arith.constant {handshake.name = "constant9"} 2 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c3_i32_1 = arith.constant {handshake.name = "constant11"} 3 : i32
    %16 = arith.shli %13, %c1_i32_0 {handshake.name = "shli0"} : i32
    %17 = arith.shli %12, %c2_i32 {handshake.name = "shli1"} : i32
    %18 = arith.xori %16, %17 {handshake.name = "xori1"} : i32
    %19 = arith.shli %15, %c3_i32_1 {handshake.name = "shli2"} : i32
    %20 = arith.xori %18, %19 {handshake.name = "xori2"} : i32
    %21 = arith.xori %20, %14 {handshake.name = "xori3"} : i32
    return {handshake.name = "return0"} %21 : i32
  }
}

