module {
  func.func @video_filter(%arg0: i32, %arg1: i32, %arg2: memref<900xi32>, %arg3: memref<900xi32>, %arg4: memref<900xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c4_i32 = arith.constant 4 : i32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.extui %0 : i32 to i64
    %6 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%7: i32):  // 2 preds: ^bb1, ^bb2
    %8 = arith.extui %7 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %9 = arith.muli %1, %c30_i64 : i64
    %10 = arith.addi %9, %8 : i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg2[%11] {handshake.name = "load0"} : memref<900xi32>
    %13 = arith.subi %12, %arg0 : i32
    %14 = arith.muli %13, %arg1 : i32
    %15 = arith.shrsi %14, %c4_i32 : i32
    %16 = arith.extui %7 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %17 = arith.muli %2, %c30_i64_0 : i64
    %18 = arith.addi %17, %16 : i64
    %19 = arith.index_cast %18 : i64 to index
    memref.store %15, %arg2[%19] {handshake.name = "store1"} : memref<900xi32>
    %20 = arith.extui %7 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %21 = arith.muli %3, %c30_i64_1 : i64
    %22 = arith.addi %21, %20 : i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg4[%23] {handshake.name = "load2"} : memref<900xi32>
    %25 = arith.subi %24, %arg0 : i32
    %26 = arith.muli %25, %arg1 : i32
    %27 = arith.shrsi %26, %c4_i32 : i32
    %28 = arith.extui %7 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %29 = arith.muli %4, %c30_i64_2 : i64
    %30 = arith.addi %29, %28 : i64
    %31 = arith.index_cast %30 : i64 to index
    memref.store %27, %arg4[%31] {handshake.name = "store3"} : memref<900xi32>
    %32 = arith.extui %7 : i32 to i64
    %c30_i64_3 = arith.constant 30 : i64
    %33 = arith.muli %5, %c30_i64_3 : i64
    %34 = arith.addi %33, %32 : i64
    %35 = arith.index_cast %34 : i64 to index
    %36 = memref.load %arg3[%35] {handshake.name = "load4"} : memref<900xi32>
    %37 = arith.subi %36, %arg0 : i32
    %38 = arith.muli %37, %arg1 : i32
    %39 = arith.shrsi %38, %c4_i32 : i32
    %40 = arith.extui %7 : i32 to i64
    %c30_i64_4 = arith.constant 30 : i64
    %41 = arith.muli %6, %c30_i64_4 : i64
    %42 = arith.addi %41, %40 : i64
    %43 = arith.index_cast %42 : i64 to index
    memref.store %39, %arg3[%43] {handshake.name = "store5"} : memref<900xi32>
    %44 = arith.addi %7, %c1_i32 : i32
    %45 = arith.cmpi ne, %44, %c30_i32 : i32
    cf.cond_br %45, ^bb2(%44 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %46 = arith.addi %0, %c1_i32 : i32
    %47 = arith.cmpi ne, %46, %c30_i32 : i32
    cf.cond_br %47, ^bb1(%46 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
