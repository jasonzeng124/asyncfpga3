module {
  func.func @kmp(%arg0: memref<4xi8>, %arg1: memref<1000xi8>, %arg2: memref<4xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c4_i32 = arith.constant 4 : i32
    %c3_i32 = arith.constant 3 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    %c0 = arith.constant 0 : index
    memref.store %c0_i32, %arg2[%c0] {handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : memref<4xi32>
    cf.br ^bb1(%c0_i32, %c1_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb4
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load1"} : memref<4xi8>
    %5 = arith.cmpi sgt, %0, %c0_i32 : i32
    cf.cond_br %5, ^bb2(%0 : i32), ^bb4(%0 : i32)
  ^bb2(%6: i32):  // 2 preds: ^bb1, ^bb3
    %7 = arith.extsi %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load2"} : memref<4xi8>
    %10 = arith.cmpi eq, %9, %4 : i8
    cf.cond_br %10, ^bb4(%6 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %11 = arith.extui %1 : i32 to i64
    %12 = arith.index_cast %11 : i64 to index
    %13 = memref.load %arg2[%12] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : memref<4xi32>
    %14 = arith.cmpi sgt, %13, %c0_i32 : i32
    cf.cond_br %14, ^bb2(%13 : i32), ^bb4(%13 : i32)
  ^bb4(%15: i32):  // 3 preds: ^bb1, ^bb2, ^bb3
    %16 = arith.extsi %15 : i32 to i64
    %17 = arith.index_cast %16 : i64 to index
    %18 = memref.load %arg0[%17] {handshake.name = "load4"} : memref<4xi8>
    %19 = arith.cmpi eq, %18, %4 : i8
    %20 = arith.addi %15, %c1_i32 : i32
    %21 = arith.select %19, %20, %15 : i32
    %22 = arith.extui %1 : i32 to i64
    %23 = arith.index_cast %22 : i64 to index
    memref.store %21, %arg2[%23] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<4xi32>
    %24 = arith.addi %1, %c1_i32 : i32
    %25 = arith.cmpi ult, %24, %c4_i32 : i32
    cf.cond_br %25, ^bb1(%21, %24 : i32, i32), ^bb5(%c0_i32, %c0_i32, %c0_i32 : i32, i32, i32)
  ^bb5(%26: i32, %27: i32, %28: i32):  // 2 preds: ^bb4, ^bb10
    %29 = arith.extui %28 : i32 to i64
    %30 = arith.index_cast %29 : i64 to index
    %31 = memref.load %arg1[%30] {handshake.name = "load6"} : memref<1000xi8>
    %32 = arith.cmpi sgt, %27, %c0_i32 : i32
    cf.cond_br %32, ^bb6(%27 : i32), ^bb8(%27 : i32)
  ^bb6(%33: i32):  // 2 preds: ^bb5, ^bb7
    %34 = arith.extsi %33 : i32 to i64
    %35 = arith.index_cast %34 : i64 to index
    %36 = memref.load %arg0[%35] {handshake.name = "load7"} : memref<4xi8>
    %37 = arith.cmpi eq, %36, %31 : i8
    cf.cond_br %37, ^bb8(%33 : i32), ^bb7
  ^bb7:  // pred: ^bb6
    %38 = arith.extsi %33 : i32 to i64
    %39 = arith.index_cast %38 : i64 to index
    %40 = memref.load %arg2[%39] {handshake.name = "load8"} : memref<4xi32>
    %41 = arith.cmpi sgt, %40, %c0_i32 : i32
    cf.cond_br %41, ^bb6(%40 : i32), ^bb8(%40 : i32)
  ^bb8(%42: i32):  // 3 preds: ^bb5, ^bb6, ^bb7
    %43 = arith.extsi %42 : i32 to i64
    %44 = arith.index_cast %43 : i64 to index
    %45 = memref.load %arg0[%44] {handshake.name = "load9"} : memref<4xi8>
    %46 = arith.cmpi eq, %45, %31 : i8
    %47 = arith.addi %42, %c1_i32 : i32
    %48 = arith.select %46, %47, %42 : i32
    %49 = arith.cmpi sgt, %48, %c3_i32 : i32
    cf.cond_br %49, ^bb9, ^bb10(%48, %26 : i32, i32)
  ^bb9:  // pred: ^bb8
    %50 = arith.addi %26, %c1_i32 : i32
    %51 = arith.addi %48, %c-1_i32 : i32
    %52 = arith.extsi %51 : i32 to i64
    %53 = arith.index_cast %52 : i64 to index
    %54 = memref.load %arg2[%53] {handshake.name = "load10"} : memref<4xi32>
    cf.br ^bb10(%54, %50 : i32, i32)
  ^bb10(%55: i32, %56: i32):  // 2 preds: ^bb8, ^bb9
    %57 = arith.addi %28, %c1_i32 : i32
    %58 = arith.cmpi ult, %57, %c1000_i32 : i32
    cf.cond_br %58, ^bb5(%56, %55, %57 : i32, i32, i32), ^bb11(%56 : i32)
  ^bb11(%59: i32):  // pred: ^bb10
    return %59 : i32
  }
}
