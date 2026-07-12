import { defineConfig } from '@playwright/test';
import path from 'path';

export default defineConfig({
  testDir: './e2e',
  timeout: 30000,
  retries: 0,
  workers: 1, // Extensions require serial execution (single browser context)
  use: {
    // Headless by default: the fixtures launch the FULL Chromium binary
    // (channel 'chromium', new headless), which supports MV3 extensions —
    // the headless-shell binary behind plain `headless: true` does not.
    // Set HEADED=1 for visible windows while debugging.
    headless: !process.env.HEADED,
  },
  projects: [{
    name: 'chromium',
    use: {
      launchOptions: {
        args: [
          `--disable-extensions-except=${path.resolve(__dirname, '..')}`,
          `--load-extension=${path.resolve(__dirname, '..')}`,
          '--no-first-run',
          '--disable-gpu',
        ],
      },
    },
  }],
});
