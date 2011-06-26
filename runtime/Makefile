ifndef ZAPF_PATH
$(error "You must set ZAPF_PATH to your zapf binary directory.")
endif

all: runtime.z5

runtime.z5: runtime.zap header.zap globals.zap empty_heap.zap
	mono $(ZAPF_PATH)/zapf.exe -i $<

clean:
	rm -f runtime.z5

