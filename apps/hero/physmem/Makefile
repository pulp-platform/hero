.PHONY: all
all: example

example: example.cc $(wildcard inc/*)
	$(CXX) -std=c++11 -Wall -Iinc $< -o $@

.PHONY: clean
clean:
	rm -f example
