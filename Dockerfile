# define base image as devcontainer and codespace target
FROM topologytoolkit/ttk-dev:5.10.1 as dev

# build and install TTK such that it is available pvserver and pvbatch
FROM dev as install

COPY / /ttk/
RUN cmake -B /build -S /ttk --preset Benchmark \
 && cmake --build /build \
 && cmake --install /build \
 && mv /ttk/data /ttk/run-benchmark.sh / \
 && rm -rf /build /ttk

CMD ["/bin/bash", "/run-benchmark.sh"]