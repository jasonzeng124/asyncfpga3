module {
  func.func @fold64(%arg0: i64 {handshake.arg_name = "v"}) -> i32 {
    %c255_i32 = arith.constant {handshake.name = "constant0"} 255 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %c81985529216486895_i64 = arith.constant {handshake.name = "constant2"} 81985529216486895 : i64
    %0 = arith.trunci %arg0 {handshake.name = "trunci0"} : i64 to i32
    %1 = arith.andi %0, %c255_i32 {handshake.name = "andi0"} : i32
    %2 = arith.cmpi ugt, %1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %2, ^bb1(%c0_i32, %arg0, %c81985529216486895_i64 : i32, i64, i64), ^bb2(%c81985529216486895_i64 : i64) {handshake.name = "cond_br0"}
  ^bb1(%3: i32, %4: i64, %5: i64):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant8"} 1 : i32
    %c11_i64 = arith.constant {handshake.name = "constant9"} 11 : i64
    %c3_i64 = arith.constant {handshake.name = "constant10"} 3 : i64
    %c7_i64 = arith.constant {handshake.name = "constant11"} 7 : i64
    %6 = arith.shli %5, %c7_i64 {handshake.name = "shli0"} : i64
    %7 = arith.xori %4, %6 {handshake.name = "xori0"} : i64
    %8 = arith.addi %5, %7 {handshake.name = "addi0"} : i64
    %9 = arith.cmpi ult, %8, %4 {handshake.name = "cmpi1"} : i64
    %10 = arith.shrui %4, %c3_i64 {handshake.name = "shrui0"} : i64
    %11 = arith.addi %8, %10 {handshake.name = "addi1"} : i64
    %12 = arith.select %9, %11, %8 {handshake.name = "select0"} : i64
    %13 = arith.shrui %4, %c11_i64 {handshake.name = "shrui1"} : i64
    %14 = arith.xori %4, %13 {handshake.name = "xori1"} : i64
    %15 = arith.addi %3, %c1_i32 {handshake.name = "addi2"} : i32
    %16 = arith.cmpi ne, %15, %1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %16, ^bb1(%15, %14, %12 : i32, i64, i64), ^bb2(%12 : i64) {handshake.name = "cond_br1"}
  ^bb2(%17: i64):  // 2 preds: ^bb0, ^bb1
    %c32_i64 = arith.constant {handshake.name = "constant12"} 32 : i64
    %18 = arith.shrui %17, %c32_i64 {handshake.name = "shrui2"} : i64
    %19 = arith.xori %17, %18 {handshake.name = "xori2"} : i64
    %20 = arith.trunci %19 {handshake.name = "trunci1"} : i64 to i32
    return {handshake.name = "return0"} %20 : i32
  }
}

