module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  func.func @nested_loop(%arg0: memref<1000xi32> {handshake.arg_name = "a"}, %arg1: memref<1000xi32> {handshake.arg_name = "b"}, %arg2: memref<1000xi32> {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %c8_i32 = arith.constant {handshake.name = "constant9"} 8 : i32
    %c7_i32 = arith.constant {handshake.name = "constant10"} 7 : i32
    %c4_i32 = arith.constant {handshake.name = "constant11"} 4 : i32
    %1 = arith.shli %0, %c4_i32 {handshake.name = "shli0"} : i32
    %2 = arith.shli %0, %c7_i32 {handshake.name = "shli1"} : i32
    %3 = arith.shli %0, %c8_i32 {handshake.name = "shli2"} : i32
    %4 = arith.addi %2, %3 {handshake.name = "addi3"} : i32
    %5 = arith.addi %1, %4 {handshake.name = "addi4"} : i32
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%6: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32 = arith.constant {handshake.name = "constant12"} 1 : i32
    %c1000_i32 = arith.constant {handshake.name = "constant13"} 1000 : i32
    %7 = arith.extui %6 {handshake.name = "extui0"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast0"} : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load0"} : memref<1000xi32>
    %10 = arith.extui %6 {handshake.name = "extui1"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast1"} : i64 to index
    %12 = memref.load %arg1[%11] {handshake.name = "load1"} : memref<1000xi32>
    %13 = arith.muli %9, %12 {handshake.name = "muli1"} : i32
    %14 = arith.addi %6, %5 {handshake.name = "addi0"} : i32
    %15 = arith.extui %14 {handshake.name = "extui2"} : i32 to i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast2"} : i64 to index
    memref.store %13, %arg2[%16] {handshake.name = "store2"} : memref<1000xi32>
    %17 = arith.cmpi slt, %13, %c1000_i32 {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.name = "cmpi0"} : i32
    %18 = arith.addi %6, %c1_i32 {handshake.name = "addi1"} : i32
    cf.cond_br %17, ^bb2(%18 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c2_i32 = arith.constant {handshake.name = "constant14"} 2 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant15"} 1 : i32
    %19 = arith.addi %0, %c1_i32_1 {handshake.name = "addi2"} : i32
    %20 = arith.cmpi ult, %19, %c2_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %20, ^bb1(%19 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

