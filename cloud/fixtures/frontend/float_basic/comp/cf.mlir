module {
  func.func @float_basic(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<30xf32>, %arg3: memref<30xf32>) {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 0.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb6
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%cst, %c0_i32 : f32, i32)
  ^bb2(%3: f32, %4: i32):  // 2 preds: ^bb1, ^bb5
    %5 = arith.extui %4 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    %7 = memref.load %arg3[%6] {handshake.name = "load0"} : memref<30xf32>
    %8 = arith.extui %4 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %9 = arith.muli %1, %c30_i64 : i64
    %10 = arith.addi %9, %8 : i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg0[%11] {handshake.name = "load1"} : memref<900xf32>
    %13 = arith.extui %4 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %14 = arith.muli %2, %c30_i64_0 : i64
    %15 = arith.addi %14, %13 : i64
    %16 = arith.index_cast %15 : i64 to index
    %17 = memref.load %arg1[%16] {handshake.name = "load2"} : memref<900xf32>
    %18 = arith.cmpf ugt, %12, %17 : f32
    cf.cond_br %18, ^bb4, ^bb3
  ^bb3:  // pred: ^bb2
    %19 = arith.extui %0 : i32 to i64
    %20 = arith.extui %4 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %21 = arith.muli %19, %c30_i64_1 : i64
    %22 = arith.addi %21, %20 : i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg0[%23] {handshake.name = "load3"} : memref<900xf32>
    %25 = arith.divf %24, %7 : f32
    %26 = arith.addf %3, %25 : f32
    cf.br ^bb5(%26 : f32)
  ^bb4:  // pred: ^bb2
    %27 = arith.extui %0 : i32 to i64
    %28 = arith.extui %4 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %29 = arith.muli %27, %c30_i64_2 : i64
    %30 = arith.addi %29, %28 : i64
    %31 = arith.index_cast %30 : i64 to index
    %32 = memref.load %arg1[%31] {handshake.name = "load4"} : memref<900xf32>
    %33 = arith.mulf %32, %7 : f32
    %34 = arith.subf %3, %33 : f32
    cf.br ^bb5(%34 : f32)
  ^bb5(%35: f32):  // 2 preds: ^bb3, ^bb4
    %36 = arith.addi %4, %c1_i32 : i32
    %37 = arith.cmpi ult, %36, %c30_i32 : i32
    cf.cond_br %37, ^bb2(%35, %36 : f32, i32), ^bb6(%35 : f32)
  ^bb6(%38: f32):  // pred: ^bb5
    %39 = arith.extui %0 : i32 to i64
    %40 = arith.index_cast %39 : i64 to index
    memref.store %38, %arg2[%40] {handshake.name = "store5"} : memref<30xf32>
    %41 = arith.addi %0, %c1_i32 : i32
    %42 = arith.cmpi ult, %41, %c30_i32 : i32
    cf.cond_br %42, ^bb1(%41 : i32), ^bb7
  ^bb7:  // pred: ^bb6
    return
  }
}
