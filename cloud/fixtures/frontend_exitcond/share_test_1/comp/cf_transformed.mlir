module {
  func.func @share_test_1(%arg0: memref<1000xi32> {handshake.arg_name = "a"}, %arg1: memref<1000xi32> {handshake.arg_name = "b"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %c1000_i32 = arith.constant {handshake.name = "constant6"} 1000 : i32
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c999_i32 = arith.constant {handshake.name = "constant8"} 999 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant9"} 0 : i32
    %c2_i32 = arith.constant {handshake.name = "constant10"} 2 : i32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.subi %c999_i32, %1 {handshake.name = "subi0"} : i32
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i32 to index
    %7 = memref.load %arg1[%6] {handshake.name = "load1"} : memref<1000xi32>
    %8 = arith.muli %4, %7 {handshake.name = "muli0"} : i32
    %9 = arith.shli %8, %c2_i32 {handshake.name = "shli0"} : i32
    %10 = arith.addi %8, %9 {handshake.name = "addi4"} : i32
    %11 = arith.addi %0, %10 {handshake.name = "addi0"} : i32
    %12 = arith.addi %1, %c1_i32 {handshake.name = "addi1"} : i32
    %13 = arith.cmpi ne, %12, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %13, ^bb1(%11, %12 : i32, i32), ^bb2(%11, %c0_i32_0 : i32, i32) {handshake.name = "cond_br0"}
  ^bb2(%14: i32, %15: i32):  // 2 preds: ^bb1, ^bb2
    %c1000_i32_1 = arith.constant {handshake.name = "constant11"} 1000 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant12"} 1 : i32
    %c999_i32_3 = arith.constant {handshake.name = "constant13"} 999 : i32
    %16 = arith.subi %c999_i32_3, %15 {handshake.name = "subi1"} : i32
    %17 = arith.index_cast %16 {handshake.name = "index_cast2"} : i32 to index
    %18 = memref.load %arg0[%17] {handshake.name = "load2"} : memref<1000xi32>
    %19 = arith.extui %15 {handshake.name = "extui1"} : i32 to i64
    %20 = arith.index_cast %19 {handshake.name = "index_cast3"} : i64 to index
    %21 = memref.load %arg1[%20] {handshake.name = "load3"} : memref<1000xi32>
    %22 = arith.muli %18, %21 {handshake.name = "muli2"} : i32
    %23 = arith.addi %14, %22 {handshake.name = "addi2"} : i32
    %24 = arith.addi %15, %c1_i32_2 {handshake.name = "addi3"} : i32
    %25 = arith.cmpi ne, %24, %c1000_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %25, ^bb2(%23, %24 : i32, i32), ^bb3(%23 : i32) {handshake.name = "cond_br1"}
  ^bb3(%26: i32):  // pred: ^bb2
    return {handshake.name = "return0"} %26 : i32
  }
}

