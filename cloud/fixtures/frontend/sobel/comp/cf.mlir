module {
  func.func @sobel(%arg0: memref<256xi32>, %arg1: memref<9xi32>, %arg2: memref<9xi32>, %arg3: memref<256xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c5_i32 = arith.constant 5 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c3_i32 = arith.constant 3 : i32
    %c4_i32 = arith.constant 4 : i32
    %c1_i32 = arith.constant 1 : i32
    %c2_i32 = arith.constant 2 : i32
    %c255_i32 = arith.constant 255 : i32
    %c15_i32 = arith.constant 15 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb11
    cf.br ^bb2(%0, %c0_i32 : i32, i32)
  ^bb2(%2: i32, %3: i32):  // 2 preds: ^bb1, ^bb10
    %4 = arith.cmpi slt, %3, %c5_i32 : i32
    cf.cond_br %4, ^bb4, ^bb3
  ^bb3:  // pred: ^bb2
    %5 = arith.cmpi eq, %3, %c5_i32 : i32
    cf.cond_br %5, ^bb10(%2 : i32), ^bb5
  ^bb4:  // pred: ^bb2
    %6 = arith.cmpi eq, %3, %c0_i32 : i32
    cf.cond_br %6, ^bb10(%2 : i32), ^bb5
  ^bb5:  // 2 preds: ^bb3, ^bb4
    %7 = arith.extui %3 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load0"} : memref<256xi32>
    %10 = arith.extui %3 : i32 to i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg0[%11] {handshake.name = "load1"} : memref<256xi32>
    cf.br ^bb6(%c-1_i32, %c0_i32, %c0_i32 : i32, i32, i32)
  ^bb6(%13: i32, %14: i32, %15: i32):  // 2 preds: ^bb5, ^bb8
    %16 = arith.muli %13, %c3_i32 : i32
    %17 = arith.muli %13, %c3_i32 : i32
    cf.br ^bb7(%c-1_i32, %14, %15 : i32, i32, i32)
  ^bb7(%18: i32, %19: i32, %20: i32):  // 2 preds: ^bb6, ^bb7
    %21 = arith.addi %16, %18 : i32
    %22 = arith.addi %21, %c4_i32 : i32
    %23 = arith.extsi %22 : i32 to i64
    %24 = arith.index_cast %23 : i64 to index
    %25 = memref.load %arg2[%24] {handshake.name = "load2"} : memref<9xi32>
    %26 = arith.muli %9, %25 : i32
    %27 = arith.addi %19, %26 : i32
    %28 = arith.addi %17, %18 : i32
    %29 = arith.addi %28, %c4_i32 : i32
    %30 = arith.extsi %29 : i32 to i64
    %31 = arith.index_cast %30 : i64 to index
    %32 = memref.load %arg1[%31] {handshake.name = "load3"} : memref<9xi32>
    %33 = arith.muli %12, %32 : i32
    %34 = arith.addi %20, %33 : i32
    %35 = arith.addi %18, %c1_i32 : i32
    %36 = arith.cmpi slt, %35, %c2_i32 : i32
    cf.cond_br %36, ^bb7(%35, %27, %34 : i32, i32, i32), ^bb8(%34, %27 : i32, i32)
  ^bb8(%37: i32, %38: i32):  // pred: ^bb7
    %39 = arith.addi %13, %c1_i32 : i32
    %40 = arith.cmpi slt, %39, %c2_i32 : i32
    cf.cond_br %40, ^bb6(%39, %38, %37 : i32, i32, i32), ^bb9(%37, %38 : i32, i32)
  ^bb9(%41: i32, %42: i32):  // pred: ^bb8
    %43 = arith.cmpi sgt, %41, %c255_i32 : i32
    %44 = arith.select %43, %c255_i32, %41 : i32
    %45 = arith.cmpi slt, %44, %c0_i32 : i32
    %46 = arith.select %45, %c0_i32, %44 : i32
    %47 = arith.cmpi sgt, %42, %c255_i32 : i32
    %48 = arith.select %47, %c255_i32, %42 : i32
    %49 = arith.cmpi slt, %48, %c0_i32 : i32
    %50 = arith.select %49, %c0_i32, %48 : i32
    %51 = arith.addi %46, %50 : i32
    %52 = arith.addi %2, %51 : i32
    cf.br ^bb10(%52 : i32)
  ^bb10(%53: i32):  // 3 preds: ^bb3, ^bb4, ^bb9
    %54 = arith.andi %53, %c255_i32 : i32
    %55 = arith.xori %54, %c255_i32 : i32
    %56 = arith.addi %3, %1 : i32
    %57 = arith.extui %56 : i32 to i64
    %58 = arith.index_cast %57 : i64 to index
    memref.store %55, %arg3[%58] {handshake.name = "store4"} : memref<256xi32>
    %59 = arith.addi %3, %c1_i32 : i32
    %60 = arith.cmpi ult, %59, %c15_i32 : i32
    cf.cond_br %60, ^bb2(%53, %59 : i32, i32), ^bb11(%53 : i32)
  ^bb11(%61: i32):  // pred: ^bb10
    %62 = arith.addi %1, %c1_i32 : i32
    %63 = arith.cmpi ult, %62, %c15_i32 : i32
    cf.cond_br %63, ^bb1(%61, %62 : i32, i32), ^bb12(%61 : i32)
  ^bb12(%64: i32):  // pred: ^bb11
    return %64 : i32
  }
}
