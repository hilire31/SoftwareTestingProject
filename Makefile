# Makefile for SPIN model checking

MODEL = port3.pml
EXEC = pan

# Default target
all: verify

# Generate the verifier source (pan.c)
pan.c: $(MODEL)
	spin -a $(MODEL)

# Compile the verifier
$(EXEC): pan.c
	gcc -o $(EXEC) pan.c

# Run the exhaustive verification
verify: $(EXEC)
	./$(EXEC) -a

# Run a random simulation instead of full verification
simulate:
	spin -run -E $(MODEL)

# Clean up generated files
clean:
	rm -f pan pan.* *.trail *.tmp *.pml~ *.out

.PHONY: all verify simulate clean
