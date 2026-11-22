module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  func.func @loop_path(%arg0: memref<1000xi32> {handshake.arg_name = "a"}, %arg1: memref<1000xi32> {handshake.arg_name = "b"}, %arg2: memref<1000xi32> {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant6"} 1 : i32
    %c999_i32 = arith.constant {handshake.name = "constant7"} 999 : i32
    %c1000_i32 = arith.constant {handshake.name = "constant8"} 1000 : i32
    %c2_i32 = arith.constant {handshake.name = "constant9"} 2 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast1"} : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load1"} : memref<1000xi32>
    %7 = arith.addi %3, %6 {handshake.name = "addi0"} : i32
    %8 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast2"} : i64 to index
    memref.store %7, %arg2[%9] {handshake.name = "store2"} : memref<1000xi32>
    %10 = arith.subi %c1000_i32, %7 {handshake.name = "subi0"} : i32
    %11 = arith.shli %7, %c2_i32 {handshake.name = "shli0"} : i32
    %12 = arith.addi %7, %11 {handshake.name = "addi2"} : i32
    %13 = arith.cmpi sgt, %10, %12 {handshake.name = "cmpi0"} : i32
    %14 = arith.cmpi ult, %0, %c999_i32 {handshake.name = "cmpi1"} : i32
    %15 = arith.andi %13, %14 {handshake.name = "andi0"} : i1
    %16 = "dynamatic.producer_output_attr_marker"(%15) {dynamatic.speculate = {max_predictions = 4 : i64, style = "standard"}, handshake.name = "producer_output_attr_marker0"} : (i1) -> i1
    %17 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    cf.cond_br %16, ^bb1(%17 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}

