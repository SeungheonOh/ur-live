import type { Metadata } from 'next';
import './globals.css';

export const metadata: Metadata = {
  title: 'Vr playground',
  description:
    'Compile Ur to JavaScript locally with the Vr WebAssembly compiler.',
  icons: { icon: '/favicon.svg' },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
