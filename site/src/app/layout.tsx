import type { Metadata } from 'next'
import { ThemeProvider } from 'next-themes'
import { siteConfig } from '@/config/proofs'
import '@hanzo/font/css'
import './global.css'

export const metadata: Metadata = {
  title: `${siteConfig.name} Formal Proofs`,
  description: siteConfig.description,
  openGraph: {
    title: `${siteConfig.name} Formal Proofs`,
    description: siteConfig.description,
    url: 'https://proofs.lux.network',
    siteName: `${siteConfig.name} Proofs`,
    type: 'website',
  },
  twitter: {
    card: 'summary_large_image',
    title: `${siteConfig.name} Formal Proofs`,
    description: siteConfig.description,
  },
}

export default function RootLayout({
  children,
}: {
  children: React.ReactNode
}) {
  return (
    <html lang="en" suppressHydrationWarning>
      <head>
        <script
          dangerouslySetInnerHTML={{
            __html: `(function(){try{var d=document.documentElement;var s=localStorage.getItem('lux-proofs-theme');if(s==='dark'||(s!=='light'&&window.matchMedia('(prefers-color-scheme:dark)').matches)){d.classList.add('dark')}else{d.classList.remove('dark')}}catch(e){}})()`,
          }}
        />
      </head>
      <body className="min-h-svh bg-background font-sans antialiased">
        <ThemeProvider
          attribute="class"
          defaultTheme="dark"
          storageKey="lux-proofs-theme"
          enableSystem
        >
          {children}
        </ThemeProvider>
      </body>
    </html>
  )
}
