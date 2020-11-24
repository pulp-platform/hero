make all
make -C test all
make -C freepdk45/synopsys synth_snitch
make -C freepdk45/synopsys synth_snitch_cc
make -C freepdk45/synopsys synth_simple
make -C freepdk45/synopsys synth_axi_dma
make -C freepdk45/synopsys synth_foobar
make -j 5 -C moore moore_a2o_core \
moore_axi_dma \
moore_foobar \
moore_simple \
moore_snitch_cluster
make -j 5 -C sv2v sv2v_a2o_core \
sv2v_axi_dma \
sv2v_foobar \
sv2v_simple \
sv2v_snitch_cluster
make -j 5 -C verible verible_a2o_core \
verible_axi_dma \
verible_foobar \
verible_simple \
verible_snitch_cluster
make -j 5 -C spyglass spyglass_a2o_core \
spyglass_axi_dma \
spyglass_foobar \
spyglass_simple \
spyglass_snitch_cluster
