This repository consists in a verified timer driver written in Cogent, 
exploiting the Dargent extension. The implementation is based on the 
C driver available at https://github.com/seL4/util_libs/blob/c446df1f1a3e6aa1418a64a8f4db1ec615eae3c4/libplatsupport/src/plat/odroidc2/meson_timer.c.

For reference, the original driver is available in the subdirectory
 `original_C_driver`.

For the verification, the cogent driver requires specific versions of
cogent and AutoCorres (available as submodules in this repository):
- https://github.com/amblafont/cogent/tree/dargentfull
- https://github.com/amblafont/AutoCorres

For more information about the cogent driver, see the 
`verified_cogent_driver` subdirectory.


