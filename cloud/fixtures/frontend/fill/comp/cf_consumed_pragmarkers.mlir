module {
  func.func @fill(%arg0: memref<32xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}, %arg2: i32 {handshake.arg_name = "x"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c3_i32 = arith.constant {handshake.name = "constant1"} 3 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c3_i32, %arg2, %c0_i32 : i32, i32, i32, i32), ^bb2(%c0_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32, %3: i32, %4: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant6"} 1 : i32
    %c31_i32 = arith.constant {handshake.name = "constant7"} 31 : i32
    %c7_i32 = arith.constant {handshake.name = "constant8"} 7 : i32
    %c5_i32 = arith.constant {handshake.name = "constant9"} 5 : i32
    %c3_i32_0 = arith.constant {handshake.name = "constant10"} 3 : i32
    %5 = arith.shli %3, %c5_i32 {handshake.name = "shli0"} : i32
    %6 = arith.xori %3, %5 {handshake.name = "xori0"} : i32
    %7 = arith.addi %6, %1 {handshake.name = "addi0"} : i32
    %8 = arith.extui %2 {handshake.name = "extui0"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast0"} : i64 to index
    memref.store %7, %arg0[%9] {handshake.name = "store0"} : memref<32xi32>
    %10 = arith.addi %2, %c7_i32 {handshake.name = "addi1"} : i32
    %11 = arith.andi %10, %c31_i32 {handshake.name = "andi0"} : i32
    %12 = arith.shrsi %7, %c3_i32_0 {handshake.name = "shrsi0"} : i32
    %13 = arith.addi %4, %12 {handshake.name = "addi2"} : i32
    %14 = arith.addi %1, %c1_i32 {handshake.name = "addi3"} : i32
    %15 = arith.cmpi slt, %14, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %15, ^bb1(%14, %11, %7, %13 : i32, i32, i32, i32), ^bb2(%13 : i32) {handshake.name = "cond_br1"}
  ^bb2(%16: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %16 : i32
  }
}

