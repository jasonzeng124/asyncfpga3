module {
  func.func @mvt_float(%arg0: memref<900xf32>, %arg1: memref<30xf32>, %arg2: memref<30xf32>, %arg3: memref<30xf32>, %arg4: memref<30xf32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg1[%2] {handshake.name = "load0"} : memref<30xf32>
    %4 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%3, %c0_i32 : f32, i32)
  ^bb2(%5: f32, %6: i32):  // 2 preds: ^bb1, ^bb2
    %7 = arith.extui %6 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %8 = arith.muli %4, %c30_i64 : i64
    %9 = arith.addi %8, %7 : i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg0[%10] {handshake.name = "load1"} : memref<900xf32>
    %12 = arith.extui %6 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg3[%13] {handshake.name = "load2"} : memref<30xf32>
    %15 = arith.mulf %11, %14 : f32
    %16 = arith.addf %5, %15 : f32
    %17 = arith.addi %6, %c1_i32 : i32
    %18 = arith.cmpi ult, %17, %c30_i32 : i32
    cf.cond_br %18, ^bb2(%16, %17 : f32, i32), ^bb3(%16 : f32)
  ^bb3(%19: f32):  // pred: ^bb2
    %20 = arith.extui %0 : i32 to i64
    %21 = arith.index_cast %20 : i64 to index
    memref.store %19, %arg1[%21] {handshake.name = "store3"} : memref<30xf32>
    %22 = arith.addi %0, %c1_i32 : i32
    %23 = arith.cmpi ult, %22, %c30_i32 : i32
    cf.cond_br %23, ^bb1(%22 : i32), ^bb4(%c0_i32 : i32)
  ^bb4(%24: i32):  // 2 preds: ^bb3, ^bb6
    %25 = arith.extui %24 : i32 to i64
    %26 = arith.index_cast %25 : i64 to index
    %27 = memref.load %arg2[%26] {handshake.name = "load4"} : memref<30xf32>
    %28 = arith.extui %24 : i32 to i64
    cf.br ^bb5(%27, %c0_i32 : f32, i32)
  ^bb5(%29: f32, %30: i32):  // 2 preds: ^bb4, ^bb5
    %31 = arith.extui %30 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %32 = arith.muli %31, %c30_i64_0 : i64
    %33 = arith.addi %32, %28 : i64
    %34 = arith.index_cast %33 : i64 to index
    %35 = memref.load %arg0[%34] {handshake.name = "load5"} : memref<900xf32>
    %36 = arith.extui %30 : i32 to i64
    %37 = arith.index_cast %36 : i64 to index
    %38 = memref.load %arg4[%37] {handshake.name = "load6"} : memref<30xf32>
    %39 = arith.mulf %35, %38 : f32
    %40 = arith.addf %29, %39 : f32
    %41 = arith.addi %30, %c1_i32 : i32
    %42 = arith.cmpi ult, %41, %c30_i32 : i32
    cf.cond_br %42, ^bb5(%40, %41 : f32, i32), ^bb6(%40 : f32)
  ^bb6(%43: f32):  // pred: ^bb5
    %44 = arith.extui %24 : i32 to i64
    %45 = arith.index_cast %44 : i64 to index
    memref.store %43, %arg2[%45] {handshake.name = "store7"} : memref<30xf32>
    %46 = arith.addi %24, %c1_i32 : i32
    %47 = arith.cmpi ult, %46, %c30_i32 : i32
    cf.cond_br %47, ^bb4(%46 : i32), ^bb7
  ^bb7:  // pred: ^bb6
    return
  }
}
