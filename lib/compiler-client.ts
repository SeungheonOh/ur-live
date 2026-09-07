export type Compilation = {
  ok: boolean;
  javascript: string;
  diagnostics: string;
  milliseconds: number;
  memoryBytes: number;
};

export class CompilerClient {
  private worker: Worker;
  private ready: Promise<void>;
  private rejectReady!: (reason: Error) => void;
  private sequence = 0;
  private disposed = false;
  private pending?: {
    id: number;
    resolve: (result: Compilation) => void;
    reject: (reason: Error) => void;
    timer: ReturnType<typeof setTimeout>;
  };
  constructor(status: (message: string) => void) {
    this.worker = new Worker('/compiler-worker.mjs', { type: 'module' });
    this.ready = new Promise((resolve, reject) => {
      this.rejectReady = reject;
      this.worker.onmessage = ({ data }) => {
        if (data.type === 'ready') {
          status(
            `Compiler ready · ${(data.bytes / 1_000_000).toFixed(1)} MB WebAssembly`,
          );
          resolve();
        }
        if (data.type === 'failure') {
          status(data.message);
          reject(new Error(data.message));
        }
        if (
          data.type === 'compiled' &&
          this.pending &&
          this.pending.id === data.id
        ) {
          const pending = this.pending;
          this.pending = undefined;
          clearTimeout(pending.timer);
          pending.resolve(data);
        }
      };
      this.worker.onerror = (event) => {
        const error = new Error(
          event.message || 'Browser compiler worker failed',
        );
        status(error.message);
        reject(error);
        this.pending?.reject(error);
        if (this.pending) clearTimeout(this.pending.timer);
        this.pending = undefined;
      };
    });
    void this.ready.catch(() => {});
  }
  async compile(source: string): Promise<Compilation> {
    if (this.disposed) throw new Error('Compiler worker was stopped');
    await this.ready;
    if (this.disposed) throw new Error('Compiler worker was stopped');
    if (this.pending) throw new Error('A compilation is already running');
    return new Promise((resolve, reject) => {
      const id = ++this.sequence;
      const timer = setTimeout(
        () =>
          this.dispose(
            'Compilation exceeded 30 seconds. Try a smaller program.',
          ),
        30_000,
      );
      this.pending = { id, resolve, reject, timer };
      this.worker.postMessage({ type: 'compile', id, source });
    });
  }
  dispose(reason = 'Compilation cancelled') {
    this.disposed = true;
    this.worker.terminate();
    const error = new Error(reason);
    this.rejectReady(error);
    if (this.pending) {
      clearTimeout(this.pending.timer);
      this.pending.reject(error);
      this.pending = undefined;
    }
  }
}
