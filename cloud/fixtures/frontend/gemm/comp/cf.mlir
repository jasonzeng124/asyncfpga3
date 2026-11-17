module {
  func.func @gemm(%arg0: i32, %arg1: i32, %arg2: memref<900xi32>, %arg3: memref<900xi32>, %arg4: memref<900xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c20_i32 = arith.constant 20 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb4
    %5 = arith.extui %4 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %6 = arith.muli %1, %c30_i64 : i64
    %7 = arith.addi %6, %5 : i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg4[%8] {handshake.name = "load0"} : memref<900xi32>
    %10 = arith.muli %9, %arg1 : i32
    %11 = arith.sitofp %10 : i32 to f32
    %12 = arith.extui %4 : i32 to i64
    cf.br ^bb3(%11, %c0_i32 : f32, i32)
  ^bb3(%13: f32, %14: i32):  // 2 preds: ^bb2, ^bb3
    %15 = arith.extui %14 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %16 = arith.muli %2, %c30_i64_0 : i64
    %17 = arith.addi %16, %15 : i64
    %18 = arith.index_cast %17 : i64 to index
    %19 = memref.load %arg2[%18] {handshake.name = "load1"} : memref<900xi32>
    %20 = arith.muli %19, %arg0 : i32
    %21 = arith.extui %14 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %22 = arith.muli %21, %c30_i64_1 : i64
    %23 = arith.addi %22, %12 : i64
    %24 = arith.index_cast %23 : i64 to index
    %25 = memref.load %arg3[%24] {handshake.name = "load2"} : memref<900xi32>
    %26 = arith.muli %20, %25 : i32
    %27 = arith.sitofp %26 : i32 to f32
    %28 = arith.addf %13, %27 : f32
    %29 = arith.addi %14, %c1_i32 : i32
    %30 = arith.cmpi ult, %29, %c20_i32 : i32
    cf.cond_br %30, ^bb3(%28, %29 : f32, i32), ^bb4(%28 : f32)
  ^bb4(%31: f32):  // pred: ^bb3
    %32 = arith.fptosi %31 : f32 to i32
    %33 = arith.extui %4 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %34 = arith.muli %3, %c30_i64_2 : i64
    %35 = arith.addi %34, %33 : i64
    %36 = arith.index_cast %35 : i64 to index
    memref.store %32, %arg4[%36] {handshake.name = "store3"} : memref<900xi32>
    %37 = arith.addi %4, %c1_i32 : i32
    %38 = arith.cmpi ult, %37, %c20_i32 : i32
    cf.cond_br %38, ^bb2(%37 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %39 = arith.addi %0, %c1_i32 : i32
    %40 = arith.cmpi ult, %39, %c20_i32 : i32
    cf.cond_br %40, ^bb1(%39 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    return
  }
}
