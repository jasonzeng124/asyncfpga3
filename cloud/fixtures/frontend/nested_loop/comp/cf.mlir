module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64}
  func.func @nested_loop(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c400_i32 = arith.constant 400 : i32
    %c1000_i32 = arith.constant 1000 : i32
    %c8_i32 = arith.constant 8 : i32
    %c1_i32 = arith.constant 1 : i32
    %c2_i32 = arith.constant 2 : i32
    %0 = memref.get_global @".str" : memref<9xi8>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb3
    %2 = arith.muli %1, %c400_i32 : i32
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb2
    %4 = arith.extui %3 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg0[%5] {handshake.name = "load0"} : memref<1000xi32>
    %7 = arith.extui %3 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg1[%8] {handshake.name = "load1"} : memref<1000xi32>
    %10 = arith.muli %6, %9 : i32
    %11 = arith.addi %3, %2 : i32
    %12 = arith.extui %11 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    memref.store %10, %arg2[%13] {handshake.name = "store2"} : memref<1000xi32>
    %14 = arith.cmpi slt, %10, %c1000_i32 : i32
    %15 = "dynamatic.producer_output_attr_marker"(%14) {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}} : (i1) -> i1
    %16 = arith.addi %3, %c1_i32 : i32
    cf.cond_br %15, ^bb2(%16 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %17 = arith.addi %1, %c1_i32 : i32
    %18 = arith.cmpi ult, %17, %c2_i32 : i32
    cf.cond_br %18, ^bb1(%17 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
