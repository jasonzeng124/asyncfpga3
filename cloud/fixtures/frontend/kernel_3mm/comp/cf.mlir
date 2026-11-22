module {
  func.func @kernel_3mm(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>, %arg3: memref<100xi32>, %arg4: memref<100xi32>, %arg5: memref<100xi32>, %arg6: memref<100xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c10_i32 = arith.constant 10 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %4 = arith.extui %3 : i32 to i64
    cf.br ^bb3(%c0_i32, %c0_i32 : i32, i32)
  ^bb3(%5: i32, %6: i32):  // 2 preds: ^bb2, ^bb3
    %7 = arith.extui %6 : i32 to i64
    %c10_i64 = arith.constant 10 : i64
    %8 = arith.muli %1, %c10_i64 : i64
    %9 = arith.addi %8, %7 : i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg0[%10] {handshake.name = "load0"} : memref<100xi32>
    %12 = arith.extui %6 : i32 to i64
    %c10_i64_0 = arith.constant 10 : i64
    %13 = arith.muli %12, %c10_i64_0 : i64
    %14 = arith.addi %13, %4 : i64
    %15 = arith.index_cast %14 : i64 to index
    %16 = memref.load %arg1[%15] {handshake.name = "load1"} : memref<100xi32>
    %17 = arith.muli %11, %16 : i32
    %18 = arith.addi %5, %17 : i32
    %19 = arith.addi %6, %c1_i32 : i32
    %20 = arith.cmpi ult, %19, %c10_i32 : i32
    cf.cond_br %20, ^bb3(%18, %19 : i32, i32), ^bb4(%18 : i32)
  ^bb4(%21: i32):  // pred: ^bb3
    %22 = arith.extui %3 : i32 to i64
    %c10_i64_1 = arith.constant 10 : i64
    %23 = arith.muli %2, %c10_i64_1 : i64
    %24 = arith.addi %23, %22 : i64
    %25 = arith.index_cast %24 : i64 to index
    memref.store %21, %arg4[%25] {handshake.deps = #handshake<deps[{dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<100xi32>
    %26 = arith.addi %3, %c1_i32 : i32
    %27 = arith.cmpi ult, %26, %c10_i32 : i32
    cf.cond_br %27, ^bb2(%26 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %28 = arith.addi %0, %c1_i32 : i32
    %29 = arith.cmpi ult, %28, %c10_i32 : i32
    cf.cond_br %29, ^bb1(%28 : i32), ^bb6(%c0_i32 : i32)
  ^bb6(%30: i32):  // 2 preds: ^bb5, ^bb10
    %31 = arith.extui %30 : i32 to i64
    %32 = arith.extui %30 : i32 to i64
    cf.br ^bb7(%c0_i32 : i32)
  ^bb7(%33: i32):  // 2 preds: ^bb6, ^bb9
    %34 = arith.extui %33 : i32 to i64
    cf.br ^bb8(%c0_i32, %c0_i32 : i32, i32)
  ^bb8(%35: i32, %36: i32):  // 2 preds: ^bb7, ^bb8
    %37 = arith.extui %35 : i32 to i64
    %c10_i64_2 = arith.constant 10 : i64
    %38 = arith.muli %31, %c10_i64_2 : i64
    %39 = arith.addi %38, %37 : i64
    %40 = arith.index_cast %39 : i64 to index
    %41 = memref.load %arg2[%40] {handshake.name = "load3"} : memref<100xi32>
    %42 = arith.extui %35 : i32 to i64
    %c10_i64_3 = arith.constant 10 : i64
    %43 = arith.muli %42, %c10_i64_3 : i64
    %44 = arith.addi %43, %34 : i64
    %45 = arith.index_cast %44 : i64 to index
    %46 = memref.load %arg3[%45] {handshake.name = "load4"} : memref<100xi32>
    %47 = arith.muli %41, %46 : i32
    %48 = arith.addi %36, %47 : i32
    %49 = arith.addi %35, %c1_i32 : i32
    %50 = arith.cmpi ult, %49, %c10_i32 : i32
    cf.cond_br %50, ^bb8(%49, %48 : i32, i32), ^bb9(%48 : i32)
  ^bb9(%51: i32):  // pred: ^bb8
    %52 = arith.extui %33 : i32 to i64
    %c10_i64_4 = arith.constant 10 : i64
    %53 = arith.muli %32, %c10_i64_4 : i64
    %54 = arith.addi %53, %52 : i64
    %55 = arith.index_cast %54 : i64 to index
    memref.store %51, %arg5[%55] {handshake.deps = #handshake<deps[{dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<100xi32>
    %56 = arith.addi %33, %c1_i32 : i32
    %57 = arith.cmpi ult, %56, %c10_i32 : i32
    cf.cond_br %57, ^bb7(%56 : i32), ^bb10
  ^bb10:  // pred: ^bb9
    %58 = arith.addi %30, %c1_i32 : i32
    %59 = arith.cmpi ult, %58, %c10_i32 : i32
    cf.cond_br %59, ^bb6(%58 : i32), ^bb11(%c0_i32 : i32)
  ^bb11(%60: i32):  // 2 preds: ^bb10, ^bb15
    %61 = arith.extui %60 : i32 to i64
    %62 = arith.extui %60 : i32 to i64
    cf.br ^bb12(%c0_i32 : i32)
  ^bb12(%63: i32):  // 2 preds: ^bb11, ^bb14
    %64 = arith.extui %63 : i32 to i64
    cf.br ^bb13(%c0_i32, %c0_i32 : i32, i32)
  ^bb13(%65: i32, %66: i32):  // 2 preds: ^bb12, ^bb13
    %67 = arith.extui %65 : i32 to i64
    %c10_i64_5 = arith.constant 10 : i64
    %68 = arith.muli %61, %c10_i64_5 : i64
    %69 = arith.addi %68, %67 : i64
    %70 = arith.index_cast %69 : i64 to index
    %71 = memref.load %arg4[%70] {handshake.name = "load6"} : memref<100xi32>
    %72 = arith.extui %65 : i32 to i64
    %c10_i64_6 = arith.constant 10 : i64
    %73 = arith.muli %72, %c10_i64_6 : i64
    %74 = arith.addi %73, %64 : i64
    %75 = arith.index_cast %74 : i64 to index
    %76 = memref.load %arg5[%75] {handshake.name = "load7"} : memref<100xi32>
    %77 = arith.muli %71, %76 : i32
    %78 = arith.addi %66, %77 : i32
    %79 = arith.addi %65, %c1_i32 : i32
    %80 = arith.cmpi ult, %79, %c10_i32 : i32
    cf.cond_br %80, ^bb13(%79, %78 : i32, i32), ^bb14(%78 : i32)
  ^bb14(%81: i32):  // pred: ^bb13
    %82 = arith.extui %63 : i32 to i64
    %c10_i64_7 = arith.constant 10 : i64
    %83 = arith.muli %62, %c10_i64_7 : i64
    %84 = arith.addi %83, %82 : i64
    %85 = arith.index_cast %84 : i64 to index
    memref.store %81, %arg6[%85] {handshake.name = "store8"} : memref<100xi32>
    %86 = arith.addi %63, %c1_i32 : i32
    %87 = arith.cmpi ult, %86, %c10_i32 : i32
    cf.cond_br %87, ^bb12(%86 : i32), ^bb15
  ^bb15:  // pred: ^bb14
    %88 = arith.addi %60, %c1_i32 : i32
    %89 = arith.cmpi ult, %88, %c10_i32 : i32
    cf.cond_br %89, ^bb11(%88 : i32), ^bb16
  ^bb16:  // pred: ^bb15
    return
  }
}
