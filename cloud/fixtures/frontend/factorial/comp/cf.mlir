module {
  memref.global "private" constant @".str" : memref<17xi8> = dense<[78, 111, 32, 116, 114, 105, 118, 105, 97, 108, 32, 116, 101, 115, 116, 33, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<47xi8> = dense<[40, 40, 40, 110, 32, 62, 32, 49, 41, 32, 33, 61, 32, 48, 41, 32, 38, 32, 40, 40, 34, 78, 111, 32, 116, 114, 105, 118, 105, 97, 108, 32, 116, 101, 115, 116, 33, 34, 41, 32, 33, 61, 32, 48, 41, 41, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<42xi8> = dense<[98, 117, 105, 108, 100, 47, 102, 114, 111, 110, 116, 101, 110, 100, 47, 102, 97, 99, 116, 111, 114, 105, 97, 108, 47, 99, 111, 109, 112, 47, 102, 97, 99, 116, 111, 114, 105, 97, 108, 46, 99, 0]> {alignment = 1 : i64}
  memref.global "private" constant @__PRETTY_FUNCTION__.main : memref<15xi8> = dense<[105, 110, 116, 32, 109, 97, 105, 110, 40, 118, 111, 105, 100, 41, 0]> {alignment = 1 : i64}
  func.func @factorial(%arg0: i32) -> i32 {
    %c2_i32 = arith.constant 2 : i32
    %c1_i32 = arith.constant 1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c-2_i32 = arith.constant -2 : i32
    %c-3_i32 = arith.constant -3 : i32
    %0 = arith.cmpi sgt, %arg0, %c2_i32 : i32
    cf.cond_br %0, ^bb2(%arg0, %c1_i32 : i32, i32), ^bb1(%c1_i32, %arg0 : i32, i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb2
    %3 = arith.cmpi sgt, %2, %c0_i32 : i32
    cf.cond_br %3, ^bb3(%2, %1 : i32, i32), ^bb4(%1 : i32)
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb0, ^bb2
    %6 = arith.addi %4, %c-1_i32 : i32
    %7 = arith.muli %4, %6 : i32
    %8 = arith.addi %4, %c-2_i32 : i32
    %9 = arith.muli %7, %8 : i32
    %10 = arith.muli %5, %9 : i32
    %11 = arith.addi %4, %c-3_i32 : i32
    %12 = arith.cmpi sgt, %11, %c2_i32 : i32
    cf.cond_br %12, ^bb2(%11, %10 : i32, i32), ^bb1(%10, %11 : i32, i32)
  ^bb3(%13: i32, %14: i32):  // 2 preds: ^bb1, ^bb3
    %15 = arith.muli %14, %13 : i32
    %16 = arith.addi %13, %c-1_i32 : i32
    %17 = arith.cmpi sgt, %16, %c0_i32 : i32
    cf.cond_br %17, ^bb3(%16, %15 : i32, i32), ^bb4(%15 : i32)
  ^bb4(%18: i32):  // 2 preds: ^bb1, ^bb3
    return %18 : i32
  }
}
