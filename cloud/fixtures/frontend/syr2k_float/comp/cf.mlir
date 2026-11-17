module {
  func.func @syr2k_float(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<900xf32>, %arg3: f32, %arg4: f32) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c10_i32 = arith.constant 10 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%2: i32):  // 2 preds: ^bb1, ^bb2
    %3 = arith.extui %2 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %4 = arith.muli %1, %c30_i64 : i64
    %5 = arith.addi %4, %3 : i64
    %6 = arith.index_cast %5 : i64 to index
    %7 = memref.load %arg2[%6] {handshake.name = "load0"} : memref<900xf32>
    %8 = arith.mulf %7, %arg4 : f32
    %9 = arith.index_cast %5 : i64 to index
    memref.store %8, %arg2[%9] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<900xf32>
    %10 = arith.addi %2, %c1_i32 : i32
    %11 = arith.cmpi ult, %10, %c10_i32 : i32
    cf.cond_br %11, ^bb2(%10 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %12 = arith.addi %0, %c1_i32 : i32
    %13 = arith.cmpi ult, %12, %c10_i32 : i32
    cf.cond_br %13, ^bb1(%12 : i32), ^bb4(%c0_i32 : i32)
  ^bb4(%14: i32):  // 2 preds: ^bb3, ^bb8
    %15 = arith.extui %14 : i32 to i64
    %16 = arith.extui %14 : i32 to i64
    %17 = arith.extui %14 : i32 to i64
    %18 = arith.extui %14 : i32 to i64
    cf.br ^bb5(%c0_i32 : i32)
  ^bb5(%19: i32):  // 2 preds: ^bb4, ^bb7
    %20 = arith.extui %19 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %21 = arith.muli %15, %c30_i64_0 : i64
    %22 = arith.addi %21, %20 : i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg2[%23] {handshake.name = "load2"} : memref<900xf32>
    %25 = arith.extui %19 : i32 to i64
    %26 = arith.extui %19 : i32 to i64
    cf.br ^bb6(%24, %c0_i32 : f32, i32)
  ^bb6(%27: f32, %28: i32):  // 2 preds: ^bb5, ^bb6
    %29 = arith.extui %28 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %30 = arith.muli %16, %c30_i64_1 : i64
    %31 = arith.addi %30, %29 : i64
    %32 = arith.index_cast %31 : i64 to index
    %33 = memref.load %arg0[%32] {handshake.name = "load3"} : memref<900xf32>
    %34 = arith.mulf %33, %arg3 : f32
    %35 = arith.extui %28 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %36 = arith.muli %25, %c30_i64_2 : i64
    %37 = arith.addi %36, %35 : i64
    %38 = arith.index_cast %37 : i64 to index
    %39 = memref.load %arg1[%38] {handshake.name = "load4"} : memref<900xf32>
    %40 = arith.mulf %34, %39 : f32
    %41 = arith.addf %27, %40 : f32
    %42 = arith.extui %28 : i32 to i64
    %c30_i64_3 = arith.constant 30 : i64
    %43 = arith.muli %17, %c30_i64_3 : i64
    %44 = arith.addi %43, %42 : i64
    %45 = arith.index_cast %44 : i64 to index
    %46 = memref.load %arg1[%45] {handshake.name = "load5"} : memref<900xf32>
    %47 = arith.mulf %46, %arg3 : f32
    %48 = arith.extui %28 : i32 to i64
    %c30_i64_4 = arith.constant 30 : i64
    %49 = arith.muli %26, %c30_i64_4 : i64
    %50 = arith.addi %49, %48 : i64
    %51 = arith.index_cast %50 : i64 to index
    %52 = memref.load %arg0[%51] {handshake.name = "load6"} : memref<900xf32>
    %53 = arith.mulf %47, %52 : f32
    %54 = arith.addf %41, %53 : f32
    %55 = arith.addi %28, %c1_i32 : i32
    %56 = arith.cmpi ult, %55, %c10_i32 : i32
    cf.cond_br %56, ^bb6(%54, %55 : f32, i32), ^bb7(%54 : f32)
  ^bb7(%57: f32):  // pred: ^bb6
    %58 = arith.extui %19 : i32 to i64
    %c30_i64_5 = arith.constant 30 : i64
    %59 = arith.muli %18, %c30_i64_5 : i64
    %60 = arith.addi %59, %58 : i64
    %61 = arith.index_cast %60 : i64 to index
    memref.store %57, %arg2[%61] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store7"} : memref<900xf32>
    %62 = arith.addi %19, %c1_i32 : i32
    %63 = arith.cmpi ult, %62, %c10_i32 : i32
    cf.cond_br %63, ^bb5(%62 : i32), ^bb8
  ^bb8:  // pred: ^bb7
    %64 = arith.addi %14, %c1_i32 : i32
    %65 = arith.cmpi ult, %64, %c10_i32 : i32
    cf.cond_br %65, ^bb4(%64 : i32), ^bb9
  ^bb9:  // pred: ^bb8
    return
  }
}
