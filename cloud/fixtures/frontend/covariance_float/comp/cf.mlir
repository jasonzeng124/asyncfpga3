module {
  func.func @covariance_float(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<30xf32>) {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 0.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    %cst_0 = arith.constant 3.000000e+01 : f32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%cst, %c0_i32 : f32, i32)
  ^bb2(%2: f32, %3: i32):  // 2 preds: ^bb1, ^bb2
    %4 = arith.extui %3 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %5 = arith.muli %4, %c30_i64 : i64
    %6 = arith.addi %5, %1 : i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load0"} : memref<900xf32>
    %9 = arith.addf %2, %8 : f32
    %10 = arith.addi %3, %c1_i32 : i32
    %11 = arith.cmpi ult, %10, %c30_i32 : i32
    cf.cond_br %11, ^bb2(%9, %10 : f32, i32), ^bb3(%9 : f32)
  ^bb3(%12: f32):  // pred: ^bb2
    %13 = arith.divf %12, %cst_0 : f32
    %14 = arith.extui %0 : i32 to i64
    %15 = arith.index_cast %14 : i64 to index
    memref.store %13, %arg2[%15] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<30xf32>
    %16 = arith.addi %0, %c1_i32 : i32
    %17 = arith.cmpi ult, %16, %c30_i32 : i32
    cf.cond_br %17, ^bb1(%16 : i32), ^bb4(%c0_i32 : i32)
  ^bb4(%18: i32):  // 2 preds: ^bb3, ^bb6
    %19 = arith.extui %18 : i32 to i64
    cf.br ^bb5(%c0_i32 : i32)
  ^bb5(%20: i32):  // 2 preds: ^bb4, ^bb5
    %21 = arith.extui %20 : i32 to i64
    %22 = arith.index_cast %21 : i64 to index
    %23 = memref.load %arg2[%22] {handshake.name = "load2"} : memref<30xf32>
    %24 = arith.extui %20 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %25 = arith.muli %19, %c30_i64_1 : i64
    %26 = arith.addi %25, %24 : i64
    %27 = arith.index_cast %26 : i64 to index
    %28 = memref.load %arg0[%27] {handshake.name = "load3"} : memref<900xf32>
    %29 = arith.subf %28, %23 : f32
    %30 = arith.index_cast %26 : i64 to index
    memref.store %29, %arg0[%30] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<900xf32>
    %31 = arith.addi %20, %c1_i32 : i32
    %32 = arith.cmpi ult, %31, %c30_i32 : i32
    cf.cond_br %32, ^bb5(%31 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    %33 = arith.addi %18, %c1_i32 : i32
    %34 = arith.cmpi ult, %33, %c30_i32 : i32
    cf.cond_br %34, ^bb4(%33 : i32), ^bb7(%c0_i32 : i32)
  ^bb7(%35: i32):  // 2 preds: ^bb6, ^bb11
    cf.br ^bb8(%35 : i32)
  ^bb8(%36: i32):  // 2 preds: ^bb7, ^bb10
    %37 = arith.extui %35 : i32 to i64
    %38 = arith.extui %36 : i32 to i64
    cf.br ^bb9(%cst, %c0_i32 : f32, i32)
  ^bb9(%39: f32, %40: i32):  // 2 preds: ^bb8, ^bb9
    %41 = arith.extui %40 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %42 = arith.muli %41, %c30_i64_2 : i64
    %43 = arith.addi %42, %37 : i64
    %44 = arith.index_cast %43 : i64 to index
    %45 = memref.load %arg0[%44] {handshake.name = "load5"} : memref<900xf32>
    %46 = arith.extui %40 : i32 to i64
    %c30_i64_3 = arith.constant 30 : i64
    %47 = arith.muli %46, %c30_i64_3 : i64
    %48 = arith.addi %47, %38 : i64
    %49 = arith.index_cast %48 : i64 to index
    %50 = memref.load %arg0[%49] {handshake.name = "load6"} : memref<900xf32>
    %51 = arith.mulf %45, %50 : f32
    %52 = arith.addf %39, %51 : f32
    %53 = arith.addi %40, %c1_i32 : i32
    %54 = arith.cmpi ult, %53, %c30_i32 : i32
    cf.cond_br %54, ^bb9(%52, %53 : f32, i32), ^bb10(%52 : f32)
  ^bb10(%55: f32):  // pred: ^bb9
    %56 = arith.extui %35 : i32 to i64
    %57 = arith.extui %36 : i32 to i64
    %c30_i64_4 = arith.constant 30 : i64
    %58 = arith.muli %56, %c30_i64_4 : i64
    %59 = arith.addi %58, %57 : i64
    %60 = arith.index_cast %59 : i64 to index
    memref.store %55, %arg1[%60] {handshake.deps = #handshake<deps[{dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store7"} : memref<900xf32>
    %61 = arith.extui %36 : i32 to i64
    %62 = arith.extui %35 : i32 to i64
    %c30_i64_5 = arith.constant 30 : i64
    %63 = arith.muli %61, %c30_i64_5 : i64
    %64 = arith.addi %63, %62 : i64
    %65 = arith.index_cast %64 : i64 to index
    memref.store %55, %arg1[%65] {handshake.deps = #handshake<deps[{dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : memref<900xf32>
    %66 = arith.addi %36, %c1_i32 : i32
    %67 = arith.cmpi ult, %66, %c30_i32 : i32
    cf.cond_br %67, ^bb8(%66 : i32), ^bb11
  ^bb11:  // pred: ^bb10
    %68 = arith.addi %35, %c1_i32 : i32
    %69 = arith.cmpi ult, %68, %c30_i32 : i32
    cf.cond_br %69, ^bb7(%68 : i32), ^bb12
  ^bb12:  // pred: ^bb11
    return
  }
}
