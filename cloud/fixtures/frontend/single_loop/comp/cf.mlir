module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64}
  func.func @single_loop(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1000_i32 = arith.constant 1000 : i32
    %c7_i32 = arith.constant 7 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = memref.get_global @".str" : memref<9xi8>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.extui %1 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    %7 = memref.load %arg1[%6] {handshake.name = "load1"} : memref<1000xi32>
    %8 = arith.muli %4, %7 : i32
    %9 = arith.extui %1 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    memref.store %8, %arg2[%10] {handshake.name = "store2"} : memref<1000xi32>
    %11 = arith.cmpi slt, %8, %c1000_i32 : i32
    %12 = "dynamatic.producer_output_attr_marker"(%11) {dynamatic.speculate = {max_predictions = 7 : i64, style = "standard"}} : (i1) -> i1
    %13 = arith.addi %1, %c1_i32 : i32
    cf.cond_br %12, ^bb1(%13 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}
