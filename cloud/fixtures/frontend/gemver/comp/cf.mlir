module {
  func.func @gemver(%arg0: i32, %arg1: i32, %arg2: memref<30xi32>, %arg3: memref<30xi32>, %arg4: memref<30xi32>, %arg5: memref<30xi32>, %arg6: memref<30xi32>, %arg7: memref<30xi32>, %arg8: memref<900xi32>, %arg9: memref<30xi32>, %arg10: memref<30xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    %4 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%5: i32):  // 2 preds: ^bb1, ^bb2
    %6 = arith.extui %5 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %7 = arith.muli %1, %c30_i64 : i64
    %8 = arith.addi %7, %6 : i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg8[%9] {handshake.name = "load0"} : memref<900xi32>
    %11 = arith.index_cast %2 : i64 to index
    %12 = memref.load %arg2[%11] {handshake.name = "load1"} : memref<30xi32>
    %13 = arith.extui %5 : i32 to i64
    %14 = arith.index_cast %13 : i64 to index
    %15 = memref.load %arg3[%14] {handshake.name = "load2"} : memref<30xi32>
    %16 = arith.muli %12, %15 : i32
    %17 = arith.addi %10, %16 : i32
    %18 = arith.index_cast %3 : i64 to index
    %19 = memref.load %arg4[%18] {handshake.name = "load3"} : memref<30xi32>
    %20 = arith.extui %5 : i32 to i64
    %21 = arith.index_cast %20 : i64 to index
    %22 = memref.load %arg5[%21] {handshake.name = "load4"} : memref<30xi32>
    %23 = arith.muli %19, %22 : i32
    %24 = arith.addi %17, %23 : i32
    %25 = arith.extui %5 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %26 = arith.muli %4, %c30_i64_0 : i64
    %27 = arith.addi %26, %25 : i64
    %28 = arith.index_cast %27 : i64 to index
    memref.store %24, %arg8[%28] {handshake.deps = #handshake<deps[{dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<900xi32>
    %29 = arith.addi %5, %c1_i32 : i32
    %30 = arith.cmpi ult, %29, %c30_i32 : i32
    cf.cond_br %30, ^bb2(%29 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %31 = arith.addi %0, %c1_i32 : i32
    %32 = arith.cmpi ult, %31, %c30_i32 : i32
    cf.cond_br %32, ^bb1(%31 : i32), ^bb4(%c0_i32 : i32)
  ^bb4(%33: i32):  // 2 preds: ^bb3, ^bb6
    %34 = arith.extui %33 : i32 to i64
    %35 = arith.index_cast %34 : i64 to index
    %36 = memref.load %arg10[%35] {handshake.name = "load6"} : memref<30xi32>
    %37 = arith.extui %33 : i32 to i64
    cf.br ^bb5(%c0_i32, %36 : i32, i32)
  ^bb5(%38: i32, %39: i32):  // 2 preds: ^bb4, ^bb5
    %40 = arith.extui %38 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %41 = arith.muli %40, %c30_i64_1 : i64
    %42 = arith.addi %41, %37 : i64
    %43 = arith.index_cast %42 : i64 to index
    %44 = memref.load %arg8[%43] {handshake.name = "load7"} : memref<900xi32>
    %45 = arith.muli %44, %arg1 : i32
    %46 = arith.extui %38 : i32 to i64
    %47 = arith.index_cast %46 : i64 to index
    %48 = memref.load %arg6[%47] {handshake.name = "load8"} : memref<30xi32>
    %49 = arith.muli %45, %48 : i32
    %50 = arith.addi %39, %49 : i32
    %51 = arith.addi %38, %c1_i32 : i32
    %52 = arith.cmpi ult, %51, %c30_i32 : i32
    cf.cond_br %52, ^bb5(%51, %50 : i32, i32), ^bb6(%50 : i32)
  ^bb6(%53: i32):  // pred: ^bb5
    %54 = arith.extui %33 : i32 to i64
    %55 = arith.index_cast %54 : i64 to index
    memref.store %53, %arg10[%55] {handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store12", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store9"} : memref<30xi32>
    %56 = arith.addi %33, %c1_i32 : i32
    %57 = arith.cmpi ult, %56, %c30_i32 : i32
    cf.cond_br %57, ^bb4(%56 : i32), ^bb7(%c0_i32 : i32)
  ^bb7(%58: i32):  // 2 preds: ^bb6, ^bb7
    %59 = arith.extui %58 : i32 to i64
    %60 = arith.index_cast %59 : i64 to index
    %61 = memref.load %arg10[%60] {handshake.name = "load10"} : memref<30xi32>
    %62 = arith.extui %58 : i32 to i64
    %63 = arith.index_cast %62 : i64 to index
    %64 = memref.load %arg7[%63] {handshake.name = "load11"} : memref<30xi32>
    %65 = arith.addi %61, %64 : i32
    %66 = arith.extui %58 : i32 to i64
    %67 = arith.index_cast %66 : i64 to index
    memref.store %65, %arg10[%67] {handshake.deps = #handshake<deps[{dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store12"} : memref<30xi32>
    %68 = arith.addi %58, %c1_i32 : i32
    %69 = arith.cmpi ult, %68, %c30_i32 : i32
    cf.cond_br %69, ^bb7(%68 : i32), ^bb8(%c0_i32 : i32)
  ^bb8(%70: i32):  // 2 preds: ^bb7, ^bb10
    %71 = arith.extui %70 : i32 to i64
    %72 = arith.index_cast %71 : i64 to index
    %73 = memref.load %arg9[%72] {handshake.name = "load13"} : memref<30xi32>
    %74 = arith.extui %70 : i32 to i64
    cf.br ^bb9(%c0_i32, %73 : i32, i32)
  ^bb9(%75: i32, %76: i32):  // 2 preds: ^bb8, ^bb9
    %77 = arith.extui %75 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %78 = arith.muli %74, %c30_i64_2 : i64
    %79 = arith.addi %78, %77 : i64
    %80 = arith.index_cast %79 : i64 to index
    %81 = memref.load %arg8[%80] {handshake.name = "load14"} : memref<900xi32>
    %82 = arith.muli %81, %arg0 : i32
    %83 = arith.extui %75 : i32 to i64
    %84 = arith.index_cast %83 : i64 to index
    %85 = memref.load %arg10[%84] {handshake.name = "load15"} : memref<30xi32>
    %86 = arith.muli %82, %85 : i32
    %87 = arith.addi %76, %86 : i32
    %88 = arith.addi %75, %c1_i32 : i32
    %89 = arith.cmpi ult, %88, %c30_i32 : i32
    cf.cond_br %89, ^bb9(%88, %87 : i32, i32), ^bb10(%87 : i32)
  ^bb10(%90: i32):  // pred: ^bb9
    %91 = arith.extui %70 : i32 to i64
    %92 = arith.index_cast %91 : i64 to index
    memref.store %90, %arg9[%92] {handshake.name = "store16"} : memref<30xi32>
    %93 = arith.addi %70, %c1_i32 : i32
    %94 = arith.cmpi ult, %93, %c30_i32 : i32
    cf.cond_br %94, ^bb8(%93 : i32), ^bb11
  ^bb11:  // pred: ^bb10
    return
  }
}
