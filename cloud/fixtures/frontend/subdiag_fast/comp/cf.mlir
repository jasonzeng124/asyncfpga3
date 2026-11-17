module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64}
  func.func @subdiag_fast(%arg0: memref<1000xf32>, %arg1: memref<1000xf32>, %arg2: memref<1000xf32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %cst = arith.constant 1.000000e-03 : f32
    %c998_i32 = arith.constant 998 : i32
    %c17_i32 = arith.constant 17 : i32
    %0 = memref.get_global @".str" : memref<9xi8>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xf32>
    %5 = arith.addi %1, %c1_i32 : i32
    %6 = arith.extui %5 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg1[%7] {handshake.name = "load1"} : memref<1000xf32>
    %9 = arith.addf %4, %8 : f32
    %10 = arith.addi %1, %c1_i32 : i32
    %11 = arith.extui %10 : i32 to i64
    %12 = arith.index_cast %11 : i64 to index
    %13 = memref.load %arg2[%12] {handshake.name = "load2"} : memref<1000xf32>
    %14 = arith.mulf %9, %cst : f32
    %15 = arith.cmpf ugt, %13, %14 : f32
    %16 = arith.cmpi ult, %1, %c998_i32 : i32
    %17 = arith.andi %15, %16 : i1
    %18 = "dynamatic.producer_output_attr_marker"(%17) {dynamatic.speculate = {max_predictions = 17 : i64, style = "standard"}} : (i1) -> i1
    cf.cond_br %18, ^bb1(%10 : i32), ^bb2(%10 : i32)
  ^bb2(%19: i32):  // pred: ^bb1
    return %19 : i32
  }
}
