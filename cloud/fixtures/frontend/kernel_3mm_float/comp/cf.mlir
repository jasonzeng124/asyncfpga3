module {
  func.func @kernel_3mm_float(%arg0: memref<100xf32>, %arg1: memref<100xf32>, %arg2: memref<100xf32>, %arg3: memref<100xf32>, %arg4: memref<100xf32>, %arg5: memref<100xf32>, %arg6: memref<100xf32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c10_i32 = arith.constant 10 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb4
    %5 = arith.extui %4 : i32 to i64
    %c10_i64 = arith.constant 10 : i64
    %6 = arith.muli %1, %c10_i64 : i64
    %7 = arith.addi %6, %5 : i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg4[%8] {handshake.name = "load0"} : memref<100xf32>
    %10 = arith.extui %4 : i32 to i64
    cf.br ^bb3(%9, %c0_i32 : f32, i32)
  ^bb3(%11: f32, %12: i32):  // 2 preds: ^bb2, ^bb3
    %13 = arith.extui %12 : i32 to i64
    %c10_i64_0 = arith.constant 10 : i64
    %14 = arith.muli %2, %c10_i64_0 : i64
    %15 = arith.addi %14, %13 : i64
    %16 = arith.index_cast %15 : i64 to index
    %17 = memref.load %arg0[%16] {handshake.name = "load1"} : memref<100xf32>
    %18 = arith.extui %12 : i32 to i64
    %c10_i64_1 = arith.constant 10 : i64
    %19 = arith.muli %18, %c10_i64_1 : i64
    %20 = arith.addi %19, %10 : i64
    %21 = arith.index_cast %20 : i64 to index
    %22 = memref.load %arg1[%21] {handshake.name = "load2"} : memref<100xf32>
    %23 = arith.mulf %17, %22 : f32
    %24 = arith.addf %11, %23 : f32
    %25 = arith.addi %12, %c1_i32 : i32
    %26 = arith.cmpi ult, %25, %c10_i32 : i32
    cf.cond_br %26, ^bb3(%24, %25 : f32, i32), ^bb4(%24 : f32)
  ^bb4(%27: f32):  // pred: ^bb3
    %28 = arith.extui %4 : i32 to i64
    %c10_i64_2 = arith.constant 10 : i64
    %29 = arith.muli %3, %c10_i64_2 : i64
    %30 = arith.addi %29, %28 : i64
    %31 = arith.index_cast %30 : i64 to index
    memref.store %27, %arg4[%31] {handshake.deps = #handshake<deps[{dstAccess : "load9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<100xf32>
    %32 = arith.addi %4, %c1_i32 : i32
    %33 = arith.cmpi ult, %32, %c10_i32 : i32
    cf.cond_br %33, ^bb2(%32 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %34 = arith.addi %0, %c1_i32 : i32
    %35 = arith.cmpi ult, %34, %c10_i32 : i32
    cf.cond_br %35, ^bb1(%34 : i32), ^bb6(%c0_i32 : i32)
  ^bb6(%36: i32):  // 2 preds: ^bb5, ^bb10
    %37 = arith.extui %36 : i32 to i64
    %38 = arith.extui %36 : i32 to i64
    %39 = arith.extui %36 : i32 to i64
    cf.br ^bb7(%c0_i32 : i32)
  ^bb7(%40: i32):  // 2 preds: ^bb6, ^bb9
    %41 = arith.extui %40 : i32 to i64
    %c10_i64_3 = arith.constant 10 : i64
    %42 = arith.muli %37, %c10_i64_3 : i64
    %43 = arith.addi %42, %41 : i64
    %44 = arith.index_cast %43 : i64 to index
    %45 = memref.load %arg5[%44] {handshake.name = "load4"} : memref<100xf32>
    %46 = arith.extui %40 : i32 to i64
    cf.br ^bb8(%45, %c0_i32 : f32, i32)
  ^bb8(%47: f32, %48: i32):  // 2 preds: ^bb7, ^bb8
    %49 = arith.extui %48 : i32 to i64
    %c10_i64_4 = arith.constant 10 : i64
    %50 = arith.muli %38, %c10_i64_4 : i64
    %51 = arith.addi %50, %49 : i64
    %52 = arith.index_cast %51 : i64 to index
    %53 = memref.load %arg2[%52] {handshake.name = "load5"} : memref<100xf32>
    %54 = arith.extui %48 : i32 to i64
    %c10_i64_5 = arith.constant 10 : i64
    %55 = arith.muli %54, %c10_i64_5 : i64
    %56 = arith.addi %55, %46 : i64
    %57 = arith.index_cast %56 : i64 to index
    %58 = memref.load %arg3[%57] {handshake.name = "load6"} : memref<100xf32>
    %59 = arith.mulf %53, %58 : f32
    %60 = arith.addf %47, %59 : f32
    %61 = arith.addi %48, %c1_i32 : i32
    %62 = arith.cmpi ult, %61, %c10_i32 : i32
    cf.cond_br %62, ^bb8(%60, %61 : f32, i32), ^bb9(%60 : f32)
  ^bb9(%63: f32):  // pred: ^bb8
    %64 = arith.extui %40 : i32 to i64
    %c10_i64_6 = arith.constant 10 : i64
    %65 = arith.muli %39, %c10_i64_6 : i64
    %66 = arith.addi %65, %64 : i64
    %67 = arith.index_cast %66 : i64 to index
    memref.store %63, %arg5[%67] {handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store7"} : memref<100xf32>
    %68 = arith.addi %40, %c1_i32 : i32
    %69 = arith.cmpi ult, %68, %c10_i32 : i32
    cf.cond_br %69, ^bb7(%68 : i32), ^bb10
  ^bb10:  // pred: ^bb9
    %70 = arith.addi %36, %c1_i32 : i32
    %71 = arith.cmpi ult, %70, %c10_i32 : i32
    cf.cond_br %71, ^bb6(%70 : i32), ^bb11(%c0_i32 : i32)
  ^bb11(%72: i32):  // 2 preds: ^bb10, ^bb15
    %73 = arith.extui %72 : i32 to i64
    %74 = arith.extui %72 : i32 to i64
    %75 = arith.extui %72 : i32 to i64
    cf.br ^bb12(%c0_i32 : i32)
  ^bb12(%76: i32):  // 2 preds: ^bb11, ^bb14
    %77 = arith.extui %76 : i32 to i64
    %c10_i64_7 = arith.constant 10 : i64
    %78 = arith.muli %73, %c10_i64_7 : i64
    %79 = arith.addi %78, %77 : i64
    %80 = arith.index_cast %79 : i64 to index
    %81 = memref.load %arg6[%80] {handshake.name = "load8"} : memref<100xf32>
    %82 = arith.extui %76 : i32 to i64
    cf.br ^bb13(%81, %c0_i32 : f32, i32)
  ^bb13(%83: f32, %84: i32):  // 2 preds: ^bb12, ^bb13
    %85 = arith.extui %84 : i32 to i64
    %c10_i64_8 = arith.constant 10 : i64
    %86 = arith.muli %74, %c10_i64_8 : i64
    %87 = arith.addi %86, %85 : i64
    %88 = arith.index_cast %87 : i64 to index
    %89 = memref.load %arg4[%88] {handshake.name = "load9"} : memref<100xf32>
    %90 = arith.extui %84 : i32 to i64
    %c10_i64_9 = arith.constant 10 : i64
    %91 = arith.muli %90, %c10_i64_9 : i64
    %92 = arith.addi %91, %82 : i64
    %93 = arith.index_cast %92 : i64 to index
    %94 = memref.load %arg5[%93] {handshake.name = "load10"} : memref<100xf32>
    %95 = arith.mulf %89, %94 : f32
    %96 = arith.addf %83, %95 : f32
    %97 = arith.addi %84, %c1_i32 : i32
    %98 = arith.cmpi ult, %97, %c10_i32 : i32
    cf.cond_br %98, ^bb13(%96, %97 : f32, i32), ^bb14(%96 : f32)
  ^bb14(%99: f32):  // pred: ^bb13
    %100 = arith.extui %76 : i32 to i64
    %c10_i64_10 = arith.constant 10 : i64
    %101 = arith.muli %75, %c10_i64_10 : i64
    %102 = arith.addi %101, %100 : i64
    %103 = arith.index_cast %102 : i64 to index
    memref.store %99, %arg6[%103] {handshake.name = "store11"} : memref<100xf32>
    %104 = arith.addi %76, %c1_i32 : i32
    %105 = arith.cmpi ult, %104, %c10_i32 : i32
    cf.cond_br %105, ^bb12(%104 : i32), ^bb15
  ^bb15:  // pred: ^bb14
    %106 = arith.addi %72, %c1_i32 : i32
    %107 = arith.cmpi ult, %106, %c10_i32 : i32
    cf.cond_br %107, ^bb11(%106 : i32), ^bb16
  ^bb16:  // pred: ^bb15
    return
  }
}
