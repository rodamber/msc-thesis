# Build docker image for the development environment.
build-dev:
	docker build -t outsynth-dev-img --target dev .

# Create docker container for the development environment.
create-dev:
	docker create -it \
	--name outsynth-dev \
	--mount type=bind,source=$(PWD),target=/app \
	outsynth-dev-img

# Start docker container for the development environment.
start-dev:
	docker start -ai outsynth-dev

# Stop docker container for the development environment.
stop-dev:
	docker stop outsynth-dev

# Build docker image for the Outsynth app.
build-app:
	docker build --no-cache -t outsynth-app-img --target app .

# Run Outsynth as a docker app. Usage is `make run-app NUM_OF_EXAMPLES
# = <num_of_examples> FILE=<filename>`, where <num_of_examples> is the
# number of examples to use and <filename> is the file from where to
# read the examples.
run-app:
	docker run --rm \
	--mount type=bind,\
	source=$(shell dirname $(PWD)/$(FILE)),\
	target=/app/$(shell dirname $(FILE)),\
	readonly \
	outsynth-app-img -e $(NUM_OF_EXAMPLES) -ci 2 -ci 2 $(FILE)

clean:
	docker container rm outsynth-dev

veryclean: clean
	docker image rm outsynth-dev-img
	docker image rm outsynth-app-img

.PHONY: build-dev create-dev start stop \
	build-app run-app \
	clean veryclean
