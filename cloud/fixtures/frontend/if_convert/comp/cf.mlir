module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64}
  func.func @if_convert(%arg0: memref<200xi32>, %arg1: memref<200xi32>) {
    %c1_i32 = arith.constant 1 : i32
    %c10000_i32 = arith.constant 10000 : i32
    %c8_i32 = arith.constant 8 : i32
    %c198_i32 = arith.constant 198 : i32
    %0 = memref.get_global @".str" : memref<9xi8>
    cf.br ^bb1(%c1_i32 : i32)
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extsi %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<200xi32>
    %5 = arith.muli %1, %4 : i32
    %6 = arith.cmpi slt, %5, %c10000_i32 : i32
    %7 = "dynamatic.producer_output_attr_marker"(%6) {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}} : (i1) -> i1
    %8 = arith.addi %1, %c1_i32 : i32
    %9 = arith.select %7, %8, %1 : i32
    %10 = arith.addi %9, %c1_i32 : i32
    %11 = arith.extsi %10 : i32 to i64
    %12 = arith.index_cast %11 : i64 to index
    memref.store %c1_i32, %arg1[%12] {handshake.name = "store1"} : memref<200xi32>
    %13 = arith.cmpi slt, %9, %c198_i32 : i32
    cf.cond_br %13, ^bb1(%10 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}
