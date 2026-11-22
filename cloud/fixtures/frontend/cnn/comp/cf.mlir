module {
  func.func @cnn(%arg0: memref<38xi32>, %arg1: memref<12xi32>, %arg2: memref<43xi32>, %arg3: memref<114xi32>, %arg4: memref<120xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c10_i32 = arith.constant 10 : i32
    %c2_i32 = arith.constant 2 : i32
    %c4_i32 = arith.constant 4 : i32
    %c5_i32 = arith.constant 5 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb24
    %1 = arith.shli %0, %c1_i32 : i32
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%2: i32):  // 2 preds: ^bb1, ^bb6
    %3 = arith.muli %2, %c10_i32 : i32
    cf.br ^bb3(%c0_i32 : i32)
  ^bb3(%4: i32):  // 2 preds: ^bb2, ^bb5
    cf.br ^bb4(%c0_i32 : i32)
  ^bb4(%5: i32):  // 2 preds: ^bb3, ^bb4
    %6 = arith.shli %5, %c1_i32 : i32
    %7 = arith.addi %6, %3 : i32
    %8 = arith.addi %7, %4 : i32
    %9 = arith.addi %1, %5 : i32
    %10 = arith.extsi %9 : i32 to i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg1[%11] {handshake.name = "load0"} : memref<12xi32>
    %13 = arith.extui %8 : i32 to i64
    %14 = arith.index_cast %13 : i64 to index
    memref.store %12, %arg3[%14] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<114xi32>
    %15 = arith.addi %5, %c1_i32 : i32
    %16 = arith.cmpi ult, %15, %c2_i32 : i32
    cf.cond_br %16, ^bb4(%15 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %17 = arith.addi %4, %c1_i32 : i32
    %18 = arith.cmpi ult, %17, %c10_i32 : i32
    cf.cond_br %18, ^bb3(%17 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    %19 = arith.addi %2, %c1_i32 : i32
    %20 = arith.cmpi ult, %19, %c10_i32 : i32
    cf.cond_br %20, ^bb2(%19 : i32), ^bb7(%c0_i32 : i32)
  ^bb7(%21: i32):  // 2 preds: ^bb6, ^bb17
    cf.br ^bb8(%c0_i32 : i32)
  ^bb8(%22: i32):  // 2 preds: ^bb7, ^bb16
    %23 = arith.addi %21, %22 : i32
    %24 = arith.muli %22, %c10_i32 : i32
    cf.br ^bb9(%c0_i32 : i32)
  ^bb9(%25: i32):  // 2 preds: ^bb8, ^bb15
    cf.br ^bb10(%c0_i32 : i32)
  ^bb10(%26: i32):  // 2 preds: ^bb9, ^bb14
    %27 = arith.addi %0, %26 : i32
    %28 = arith.addi %27, %21 : i32
    %29 = arith.shli %26, %c1_i32 : i32
    %30 = arith.addi %29, %24 : i32
    %31 = arith.addi %30, %25 : i32
    %32 = arith.extui %31 : i32 to i64
    %33 = arith.index_cast %32 : i64 to index
    %34 = memref.load %arg3[%33] {handshake.name = "load2"} : memref<114xi32>
    cf.br ^bb11(%c0_i32, %34 : i32, i32)
  ^bb11(%35: i32, %36: i32):  // 2 preds: ^bb10, ^bb13
    %37 = arith.addi %23, %35 : i32
    %38 = arith.addi %37, %25 : i32
    cf.br ^bb12(%c0_i32, %36 : i32, i32)
  ^bb12(%39: i32, %40: i32):  // 2 preds: ^bb11, ^bb12
    %41 = arith.addi %28, %39 : i32
    %42 = arith.addi %41, %35 : i32
    %43 = arith.addi %38, %39 : i32
    %44 = arith.extui %42 : i32 to i64
    %45 = arith.index_cast %44 : i64 to index
    %46 = memref.load %arg2[%45] {handshake.name = "load3"} : memref<43xi32>
    %47 = arith.extui %43 : i32 to i64
    %48 = arith.index_cast %47 : i64 to index
    %49 = memref.load %arg0[%48] {handshake.name = "load4"} : memref<38xi32>
    %50 = arith.muli %46, %49 : i32
    %51 = arith.addi %40, %50 : i32
    %52 = arith.index_cast %32 : i64 to index
    memref.store %51, %arg3[%52] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<114xi32>
    %53 = arith.addi %39, %c1_i32 : i32
    %54 = arith.cmpi ult, %53, %c4_i32 : i32
    cf.cond_br %54, ^bb12(%53, %51 : i32, i32), ^bb13(%51 : i32)
  ^bb13(%55: i32):  // pred: ^bb12
    %56 = arith.addi %35, %c1_i32 : i32
    %57 = arith.cmpi ult, %56, %c4_i32 : i32
    cf.cond_br %57, ^bb11(%56, %55 : i32, i32), ^bb14
  ^bb14:  // pred: ^bb13
    %58 = arith.addi %26, %c1_i32 : i32
    %59 = arith.cmpi ult, %58, %c2_i32 : i32
    cf.cond_br %59, ^bb10(%58 : i32), ^bb15
  ^bb15:  // pred: ^bb14
    %60 = arith.addi %25, %c1_i32 : i32
    %61 = arith.cmpi ult, %60, %c10_i32 : i32
    cf.cond_br %61, ^bb9(%60 : i32), ^bb16
  ^bb16:  // pred: ^bb15
    %62 = arith.addi %22, %c1_i32 : i32
    %63 = arith.cmpi ult, %62, %c10_i32 : i32
    cf.cond_br %63, ^bb8(%62 : i32), ^bb17
  ^bb17:  // pred: ^bb16
    %64 = arith.addi %21, %c1_i32 : i32
    %65 = arith.cmpi ult, %64, %c10_i32 : i32
    cf.cond_br %65, ^bb7(%64 : i32), ^bb18
  ^bb18:  // pred: ^bb17
    %66 = arith.muli %0, %c5_i32 : i32
    cf.br ^bb19(%c0_i32 : i32)
  ^bb19(%67: i32):  // 2 preds: ^bb18, ^bb23
    %68 = arith.muli %67, %c10_i32 : i32
    %69 = arith.muli %67, %c10_i32 : i32
    %70 = arith.addi %66, %69 : i32
    cf.br ^bb20(%c0_i32 : i32)
  ^bb20(%71: i32):  // 2 preds: ^bb19, ^bb22
    %72 = arith.addi %70, %71 : i32
    %73 = arith.extui %72 : i32 to i64
    cf.br ^bb21(%c0_i32 : i32)
  ^bb21(%74: i32):  // 2 preds: ^bb20, ^bb21
    %75 = arith.shli %74, %c1_i32 : i32
    %76 = arith.addi %75, %68 : i32
    %77 = arith.addi %76, %71 : i32
    %78 = arith.extui %77 : i32 to i64
    %79 = arith.index_cast %78 : i64 to index
    %80 = memref.load %arg3[%79] {handshake.name = "load6"} : memref<114xi32>
    %81 = arith.cmpi sgt, %80, %c0_i32 : i32
    %82 = arith.select %81, %80, %c0_i32 : i32
    %83 = arith.index_cast %73 : i64 to index
    memref.store %82, %arg4[%83] {handshake.name = "store7"} : memref<120xi32>
    %84 = arith.addi %74, %c1_i32 : i32
    %85 = arith.cmpi ult, %84, %c2_i32 : i32
    cf.cond_br %85, ^bb21(%84 : i32), ^bb22
  ^bb22:  // pred: ^bb21
    %86 = arith.addi %71, %c1_i32 : i32
    %87 = arith.cmpi ult, %86, %c10_i32 : i32
    cf.cond_br %87, ^bb20(%86 : i32), ^bb23
  ^bb23:  // pred: ^bb22
    %88 = arith.addi %67, %c1_i32 : i32
    %89 = arith.cmpi ult, %88, %c10_i32 : i32
    cf.cond_br %89, ^bb19(%88 : i32), ^bb24
  ^bb24:  // pred: ^bb23
    %90 = arith.addi %0, %c1_i32 : i32
    %91 = arith.cmpi ult, %90, %c5_i32 : i32
    cf.cond_br %91, ^bb1(%90 : i32), ^bb25
  ^bb25:  // pred: ^bb24
    return
  }
}
