module {
  func.func @symm_float(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<900xf32>, %arg3: f32, %arg4: f32) {
    %c0_i32 = arith.constant 0 : i32
    %c-1_i32 = arith.constant -1 : i32
    %cst = arith.constant 0.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    %c10_i32 = arith.constant 10 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %4 = arith.muli %2, %c30_i64 : i64
    %5 = arith.addi %4, %3 : i64
    %6 = arith.extui %0 : i32 to i64
    %7 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%8: i32):  // 2 preds: ^bb1, ^bb4
    %9 = arith.addi %8, %c-1_i32 : i32
    %10 = arith.cmpi slt, %c0_i32, %9 : i32
    cf.cond_br %10, ^bb3(%cst, %c0_i32 : f32, i32), ^bb4(%cst : f32)
  ^bb3(%11: f32, %12: i32):  // 2 preds: ^bb2, ^bb3
    %13 = arith.extui %12 : i32 to i64
    %14 = arith.extui %0 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %15 = arith.muli %13, %c30_i64_0 : i64
    %16 = arith.addi %15, %14 : i64
    %17 = arith.index_cast %16 : i64 to index
    %18 = memref.load %arg0[%17] {handshake.name = "load0"} : memref<900xf32>
    %19 = arith.mulf %18, %arg3 : f32
    %20 = arith.extui %0 : i32 to i64
    %21 = arith.extui %8 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %22 = arith.muli %20, %c30_i64_1 : i64
    %23 = arith.addi %22, %21 : i64
    %24 = arith.index_cast %23 : i64 to index
    %25 = memref.load %arg1[%24] {handshake.name = "load1"} : memref<900xf32>
    %26 = arith.mulf %19, %25 : f32
    %27 = arith.extui %12 : i32 to i64
    %28 = arith.extui %8 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %29 = arith.muli %27, %c30_i64_2 : i64
    %30 = arith.addi %29, %28 : i64
    %31 = arith.index_cast %30 : i64 to index
    %32 = memref.load %arg2[%31] {handshake.name = "load2"} : memref<900xf32>
    %33 = arith.addf %32, %26 : f32
    %34 = arith.index_cast %30 : i64 to index
    memref.store %33, %arg2[%34] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<900xf32>
    %35 = arith.extui %12 : i32 to i64
    %36 = arith.extui %8 : i32 to i64
    %c30_i64_3 = arith.constant 30 : i64
    %37 = arith.muli %35, %c30_i64_3 : i64
    %38 = arith.addi %37, %36 : i64
    %39 = arith.index_cast %38 : i64 to index
    %40 = memref.load %arg1[%39] {handshake.name = "load4"} : memref<900xf32>
    %41 = arith.extui %12 : i32 to i64
    %42 = arith.extui %0 : i32 to i64
    %c30_i64_4 = arith.constant 30 : i64
    %43 = arith.muli %41, %c30_i64_4 : i64
    %44 = arith.addi %43, %42 : i64
    %45 = arith.index_cast %44 : i64 to index
    %46 = memref.load %arg0[%45] {handshake.name = "load5"} : memref<900xf32>
    %47 = arith.mulf %40, %46 : f32
    %48 = arith.addf %11, %47 : f32
    %49 = arith.addi %12, %c1_i32 : i32
    %50 = arith.cmpi slt, %49, %9 : i32
    cf.cond_br %50, ^bb3(%48, %49 : f32, i32), ^bb4(%48 : f32)
  ^bb4(%51: f32):  // 2 preds: ^bb2, ^bb3
    %52 = arith.extui %8 : i32 to i64
    %c30_i64_5 = arith.constant 30 : i64
    %53 = arith.muli %1, %c30_i64_5 : i64
    %54 = arith.addi %53, %52 : i64
    %55 = arith.index_cast %54 : i64 to index
    %56 = memref.load %arg2[%55] {handshake.name = "load6"} : memref<900xf32>
    %57 = arith.mulf %56, %arg4 : f32
    %58 = arith.index_cast %5 : i64 to index
    %59 = memref.load %arg0[%58] {handshake.name = "load7"} : memref<900xf32>
    %60 = arith.mulf %59, %arg3 : f32
    %61 = arith.extui %8 : i32 to i64
    %c30_i64_6 = arith.constant 30 : i64
    %62 = arith.muli %6, %c30_i64_6 : i64
    %63 = arith.addi %62, %61 : i64
    %64 = arith.index_cast %63 : i64 to index
    %65 = memref.load %arg1[%64] {handshake.name = "load8"} : memref<900xf32>
    %66 = arith.mulf %60, %65 : f32
    %67 = arith.addf %57, %66 : f32
    %68 = arith.mulf %51, %arg3 : f32
    %69 = arith.addf %67, %68 : f32
    %70 = arith.extui %8 : i32 to i64
    %c30_i64_7 = arith.constant 30 : i64
    %71 = arith.muli %7, %c30_i64_7 : i64
    %72 = arith.addi %71, %70 : i64
    %73 = arith.index_cast %72 : i64 to index
    memref.store %69, %arg2[%73] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store9"} : memref<900xf32>
    %74 = arith.addi %8, %c1_i32 : i32
    %75 = arith.cmpi ult, %74, %c30_i32 : i32
    cf.cond_br %75, ^bb2(%74 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %76 = arith.addi %0, %c1_i32 : i32
    %77 = arith.cmpi ult, %76, %c10_i32 : i32
    cf.cond_br %77, ^bb1(%76 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    return
  }
}
