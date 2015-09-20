test('T10890',
     extra_clean(['A.o', 'A.hi', 'B.o', 'B.hi']),
     multimod_compile, ['T10890', '-v0 -fwarn-unused-imports'])
