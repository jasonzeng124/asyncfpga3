module {
  func.func @cmpchain(%arg0: i32 {handshake.arg_name = "x"}, %arg1: i32 {handshake.arg_name = "y"}) -> i32 {
    %c268435456_i32 = arith.constant {handshake.name = "constant6"} 268435456 : i32
    %0 = arith.cmpi eq, %arg0, %arg1 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb5(%c268435456_i32 : i32), ^bb1 {handshake.name = "cond_br0"}
  ^bb1:  // pred: ^bb0
    %c536870912_i32 = arith.constant {handshake.name = "constant10"} 536870912 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant11"} -1 : i32
    %1 = arith.andi %arg0, %arg1 {handshake.name = "andi0"} : i32
    %2 = arith.cmpi sgt, %1, %c-1_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %2, ^bb2, ^bb5(%c536870912_i32 : i32) {handshake.name = "cond_br1"}
  ^bb2:  // pred: ^bb1
    %c805306368_i32 = arith.constant {handshake.name = "constant12"} 805306368 : i32
    %3 = arith.cmpi slt, %arg0, %arg1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %3, ^bb5(%c805306368_i32 : i32), ^bb3 {handshake.name = "cond_br2"}
  ^bb3:  // pred: ^bb2
    %c1073741824_i32 = arith.constant {handshake.name = "constant13"} 1073741824 : i32
    %4 = arith.cmpi ugt, %arg0, %arg1 {handshake.name = "cmpi3"} : i32
    cf.cond_br %4, ^bb5(%c1073741824_i32 : i32), ^bb4 {handshake.name = "cond_br3"}
  ^bb4:  // pred: ^bb3
    %c1342177280_i32 = arith.constant {handshake.name = "constant14"} 1342177280 : i32
    %c1879048192_i32 = arith.constant {handshake.name = "constant15"} 1879048192 : i32
    %c1610612736_i32 = arith.constant {handshake.name = "constant16"} 1610612736 : i32
    %c256_i32 = arith.constant {handshake.name = "constant17"} 256 : i32
    %c999999_i32 = arith.constant {handshake.name = "constant18"} 999999 : i32
    %5 = arith.cmpi sgt, %arg0, %c999999_i32 {handshake.name = "cmpi4"} : i32
    %6 = arith.cmpi ult, %arg0, %c256_i32 {handshake.name = "cmpi5"} : i32
    %7 = arith.select %6, %c1610612736_i32, %c1879048192_i32 {handshake.name = "select0"} : i32
    %8 = arith.select %5, %c1342177280_i32, %7 {handshake.name = "select1"} : i32
    cf.br ^bb5(%8 : i32) {handshake.name = "br0"}
  ^bb5(%9: i32):  // 5 preds: ^bb0, ^bb1, ^bb2, ^bb3, ^bb4
    %10 = arith.subi %arg0, %arg1 {handshake.name = "subi0"} : i32
    %11 = arith.xori %9, %10 {handshake.name = "xori0"} : i32
    return {handshake.name = "return0"} %11 : i32
  }
}

