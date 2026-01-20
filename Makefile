.PHONY: build install clean test check

# Build the release binary
build:
	cd cli && cargo build --release

# Install binary to ./bin/
install: build
	mkdir -p ./bin
	cp cli/target/release/lc ./bin/lc

# Clean build artifacts
clean:
	cd cli && cargo clean
	rm -f ./bin/lc

# Run tests
test:
	cd cli && cargo test

# Run cargo check (fast compilation check)
check:
	cd cli && cargo check

# Format code
fmt:
	cd cli && cargo fmt

# Run clippy lints
lint:
	cd cli && cargo clippy -- -D warnings
