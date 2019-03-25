all: test

# test_failed macro
define test_failed
TESTS := $(TESTS) $(1)
$(1): log
	@echo -n "$(1) ... "; \
	if $(2) > log/$(1).log 2>&1 ; then \
		echo "[FAILED]"; \
	else \
		echo "[OK]"; \
	fi
endef

# test_success macro
define test_success
TESTS := $(TESTS) $(1)
$(1): log out
	@echo -n "$(1) ... "; \
	@if [ -n "$(3)" ]; then \
		rm -rf "out/$(1)"; \
		mkdir -p "out/$(1)"; \
		cd "out/$(1)"; \
		echo "cd to out/$(1)"; \
		l="$(1).log"; \
		echo "A l=$$l"; \
	else \
		l="log/$(1).log"; \
	fi; \
	echo "l=$$l"; \
	echo $(2); \
	if $(2) > "$$l" 2>&1 ; then \
		echo "[OK]"; \
	else \
		echo "[FAILED]"; \
	fi
endef


# tests
IRG=../irg
PRINT_IRG=$(IRG)/print_irg

$(eval $(call test_failed,image_param,../irg/mkirg image_param.nml irg/image_param.irg))
$(eval $(call test_failed,double_param,../irg/mkirg double_param.nml irg/double_param.irg))
$(eval $(call test_failed,bad_named_param,../irg/mkirg bad_named_param.nml irg/bad_named_param.irg))
$(eval $(call test_success,for,../../../irg/mkirg ../for.nmp for.irg,for))


# goals
test: out/irg log $(TESTS)

out/irg:
	mkdir -p $@

log:
	mkdir $@

out:
	mkdir $@

clean:
	rm -rf log out include src

